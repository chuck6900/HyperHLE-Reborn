/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
//! `NSRunLoop`.
//!
//! Resources:
//! - Apple's [Threading Programming Guide](https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/Introduction/Introduction.html)

use super::{ns_port, ns_string, ns_timer, NSTimeInterval};
use crate::abi::CallFromHost;
use crate::dyld::{ConstantExports, HostConstant};
use crate::environment::ThreadId;
use crate::frameworks::audio_toolbox::audio_queue::{handle_audio_queue, AudioQueueRef};
use crate::frameworks::audio_toolbox::audio_services::tick_system_sound_completions;
use crate::frameworks::audio_toolbox::audio_unit::{render_audio_unit, AudioUnit};
use crate::frameworks::core_animation::ca_transaction;
use crate::frameworks::core_foundation::cf_run_loop::{
    kCFRunLoopCommonModes, kCFRunLoopDefaultMode, CFRunLoopRef,
};
use crate::frameworks::{core_animation, media_player, uikit};
use crate::libc::semaphore::{host_create_semaphore, sem_post, sem_t};
use crate::mem::MutPtr;
use crate::objc::{id, msg, nil, objc_classes, release, retain, Class, ClassExports, HostObject};
use crate::objc::{msg_send, SEL};
use crate::Environment;
use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant, UNIX_EPOCH};

/// `NSString*`
pub type NSRunLoopMode = id;
// FIXME: Maybe this shouldn't be the same value? See: https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/RunLoopManagement/RunLoopManagement.html
pub const NSRunLoopCommonModes: &str = kCFRunLoopCommonModes;
pub const NSDefaultRunLoopMode: &str = kCFRunLoopDefaultMode;

pub const CONSTANTS: ConstantExports = &[
    (
        "_NSRunLoopCommonModes",
        HostConstant::NSString(NSRunLoopCommonModes),
    ),
    (
        "_NSDefaultRunLoopMode",
        HostConstant::NSString(NSDefaultRunLoopMode),
    ),
];

#[derive(Default)]
pub struct ThreadLocalState {
    run_loop: id,
}

#[derive(Default)]
pub(crate) struct NSRunLoopHostObject {
    selector_objects: VecDeque<ObjectSelectorSource>,
    next_perform_sequence: u64,
    audio_units: Vec<AudioUnit>,
    /// Weak reference. Audio queue must remove itself when destroyed (TODO).
    /// They are in no particular order.
    audio_queues: Vec<AudioQueueRef>,
    /// NULL callback run loops use internal audio threads on iOS. Until those
    /// are modeled, poll these on the main thread in every active mode.
    /// They are not input sources and must not keep a mode alive.
    independent_audio_queues: Vec<AudioQueueRef>,
    /// Strong references to `NSTimer*` in no particular order. Timers are owned
    /// by the run loop. The timer must remove itself when invalidated.
    timers: Vec<id>,
    /// Strong references to `CFRunLoopSourceRef` objects (toll-free bridged
    /// via `_touchHLE_CFRunLoopSource`) currently registered in this run
    /// loop, per Apple's CFRunLoopAddSource semantics.
    pub(crate) sources: Vec<id>,
    /// Strong references to `NSPort*` objects registered via
    /// `-[NSRunLoop addPort:forMode:]`. The run loop owns its scheduled ports
    /// (per Apple's docs), so we retain them here and release on removal.
    /// touchHLE has no Mach message sources, so these ports never deliver
    /// input, but tracking them keeps ownership correct and lets apps that
    /// attach a port purely to keep `-[NSRunLoop run]` alive work.
    ports: Vec<id>,
    registrations: HashMap<id, HashSet<String>>,
    common_modes: HashSet<String>,
    activations: Vec<Activation>,
}
impl HostObject for NSRunLoopHostObject {}

/// CFRunLoopRunResult, shared with the NSRunLoop entry points.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub(crate) enum RunResult {
    Finished = 1,
    Stopped = 2,
    TimedOut = 3,
    HandledSource = 4,
}

struct Activation {
    mode: String,
    stopped: bool,
}

pub(crate) fn register_mode(env: &mut Environment, run_loop: id, object: id, mode: id) -> bool {
    let mode = ns_string::to_rust_string(env, mode).to_string();
    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .sources
        .push(object);

    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .registrations
        .entry(object)
        .or_default()
        .insert(mode)
}

pub(crate) fn unregister_mode(env: &mut Environment, run_loop: id, object: id, mode: id) -> bool {
    let mode = ns_string::to_rust_string(env, mode).to_string();
    let state = env.objc.borrow_mut::<NSRunLoopHostObject>(run_loop);
    if let Some(modes) = state.registrations.get_mut(&object) {
        modes.remove(&mode);
        if !modes.is_empty() {
            return false;
        }
    }
    state.registrations.remove(&object);
    state.sources.retain(|source| source != &object);
    true
}

fn matches_mode(state: &NSRunLoopHostObject, object: id, mode: &str) -> bool {
    state.registrations.get(&object).is_some_and(|modes| {
        modes.contains(mode)
            || (modes.contains(NSRunLoopCommonModes)
                && (mode == NSDefaultRunLoopMode || state.common_modes.contains(mode)))
    })
}

pub(crate) fn contains_in_mode(env: &Environment, run_loop: id, object: id, mode: &str) -> bool {
    matches_mode(env.objc.borrow(run_loop), object, mode)
}

pub(crate) fn registered_in_mode(env: &Environment, run_loop: id, object: id, mode: &str) -> bool {
    env.objc
        .borrow::<NSRunLoopHostObject>(run_loop)
        .registrations
        .get(&object)
        .is_some_and(|modes| modes.contains(mode))
}

fn is_common_mode(state: &NSRunLoopHostObject, mode: &str) -> bool {
    mode == NSDefaultRunLoopMode || state.common_modes.contains(mode)
}

fn mode_has_work(env: &Environment, run_loop: id, mode: &str) -> bool {
    let ui_source = env.current_thread == 0
        && env.window.is_some()
        && (mode == NSDefaultRunLoopMode || mode == "UITrackingRunLoopMode");
    let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
    ui_source || (is_common_mode(state, mode)
                && !state.audio_queues.is_empty())
                || state.selector_objects.iter().any(|request| request_matches_mode(state, request, mode))
                || state.timers.iter().any(|object| matches_mode(state, *object, mode))
                || state.ports.iter().any(|object| matches_mode(state, *object, mode))
                || state.sources.iter().any(|object| matches_mode(state, *object, mode)
                    && env.objc.borrow::<crate::frameworks::core_foundation::cf_run_loop::CFRunLoopSourceHostObject>(*object).valid)
}

pub(crate) fn stop(env: &mut Environment, run_loop: id) {
    if let Some(activation) = env
        .objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .activations
        .last_mut()
    {
        activation.stopped = true;
    }
}

pub(crate) fn current_mode(env: &Environment, run_loop: id) -> Option<String> {
    env.objc
        .borrow::<NSRunLoopHostObject>(run_loop)
        .activations
        .last()
        .map(|a| a.mode.clone())
}

pub(crate) fn add_common_mode(env: &mut Environment, run_loop: id, mode: id) {
    let mode = ns_string::to_rust_string(env, mode).to_string();
    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .common_modes
        .insert(mode);
}

// Adapted from touchHLE 94dab1c2: requests are input sources, not timers.
struct ObjectSelectorSource {
    target: id,
    selector: SEL,
    argument: id,
    semaphore: MutPtr<sem_t>,
    sequence: u64,
    modes: Vec<String>,
}

pub(crate) fn add_perform_request(
    env: &mut Environment,
    run_loop: id,
    target: id,
    selector: SEL,
    argument: id,
    should_sync: bool,
    modes: id,
) -> MutPtr<sem_t> {
    let semaphore = if should_sync {
        host_create_semaphore(env, 0)
    } else {
        MutPtr::null()
    };
    let modes = if modes == nil {
        vec![NSRunLoopCommonModes.to_string()]
    } else {
        let count: super::NSUInteger = msg![env; modes count];
        (0..count)
            .map(|i| {
                let mode: id = msg![env; modes objectAtIndex:i];
                ns_string::to_rust_string(env, mode).to_string()
            })
            .collect()
    };
    retain(env, target);
    retain(env, argument);
    let state = env.objc.borrow_mut::<NSRunLoopHostObject>(run_loop);
    let sequence = state.next_perform_sequence;
    state.next_perform_sequence = sequence.checked_add(1).expect("perform sequence exhausted");
    state.selector_objects.push_back(ObjectSelectorSource {
        target,
        selector,
        argument,
        semaphore,
        sequence,
        modes,
    });
    semaphore
}

fn request_matches_mode(
    state: &NSRunLoopHostObject,
    request: &ObjectSelectorSource,
    mode: &str,
) -> bool {
    request.modes.iter().any(|m| {
        m == mode
            || (m == NSRunLoopCommonModes
                && (mode == NSDefaultRunLoopMode || state.common_modes.contains(mode)))
    })
}

fn handle_perform_requests(env: &mut Environment, run_loop: id, mode: &str) -> bool {
    // Remove before calling guest code: callbacks may enqueue or run a nested
    // loop, and must not hold a host-object borrow across either operation.
    // A callback's newly queued requests belong to the next pass. Keep them
    // in the shared queue so a nested activation can still deliver them.
    let cutoff = env
        .objc
        .borrow::<NSRunLoopHostObject>(run_loop)
        .next_perform_sequence;
    let mut handled = false;
    loop {
        let index = {
            let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
            state.selector_objects.iter().position(|request| {
                request.sequence < cutoff && request_matches_mode(state, request, mode)
            })
        };
        let request = index.and_then(|i| {
            env.objc
                .borrow_mut::<NSRunLoopHostObject>(run_loop)
                .selector_objects
                .remove(i)
        });
        let Some(ObjectSelectorSource {
            target,
            selector,
            argument,
            semaphore,
            ..
        }) = request
        else {
            break;
        };
        handled = true;
        if selector.as_str(&env.mem).ends_with(':') {
            () = msg_send(env, (target, selector, argument));
        } else {
            () = msg_send(env, (target, selector));
        }
        release(env, target);
        release(env, argument);
        if !semaphore.is_null() {
            sem_post(env, semaphore);
        }
    }
    handled
}

pub const CLASSES: ClassExports = objc_classes! {

(env, this, _cmd);

@implementation NSRunLoop: NSObject

+ (id)mainRunLoop {
    run_loop_for_thread(env, this, 0)
}

+ (id)currentRunLoop {
    run_loop_for_thread(env, this, env.current_thread)
}

// TODO: more accessors

- (id) retain { this }
- (()) release {}
- (id) autorelease { this }

- (bool)runMode:(id)mode beforeDate:(id)limit_date {
    // Messaging nil returns zero: a missing date polls rather than waits.
    let time_limit = Some(msg![env; limit_date timeIntervalSince1970]);
    let mode_name = ns_string::to_rust_string(env, mode).to_string();
    if mode_name == NSRunLoopCommonModes || !mode_has_work(env, this, &mode_name) {
        return false;
    }
    // Once entered, returning because the last timer/source was removed is
    // still a successful run. NO means the mode could not start at all.
    run_in_mode(env, this, mode, time_limit, true);
    true
}

- (CFRunLoopRef)getCFRunLoop {
    // In our implementation these are the same type (they aren't in Apple's).
    this
}

// Adds a port as an input source to the run loop. See:
// https://developer.apple.com/documentation/foundation/nsrunloop/1417511-addport
// touchHLE has no Mach message delivery, so the port never fires an input
// source, but the run loop takes ownership of it (retains it) exactly as
// Cocoa does. Many old games attach a port only to keep `-[NSRunLoop run]`
// from returning immediately; our `run_run_loop` already loops until stopped,
// so this just needs to retain/track the port without crashing.
- (())addPort:(id)port // NSPort*
      forMode:(NSRunLoopMode)mode {
    if port == nil {
        log!("Warning: -[NSRunLoop addPort:nil forMode:] ignored");
        return;
    }
    log_dbg!(
        "[(NSRunLoop*){:?} addPort:{:?} forMode:{:?}]",
        this,
        port,
        mode,
    );
    register_mode(env, this, port, mode);
    // Avoid double-retaining the same port for the same run loop.
    if env.objc.borrow::<NSRunLoopHostObject>(this).ports.contains(&port) {
        return;
    }
    ns_port::retain_port(env, port);
    env.objc.borrow_mut::<NSRunLoopHostObject>(this).ports.push(port);
}

// Removes a port previously added with `addPort:forMode:`. See:
// https://developer.apple.com/documentation/foundation/nsrunloop/1408625-removeport
- (())removePort:(id)port // NSPort*
         forMode:(NSRunLoopMode)mode {
    if port == nil {
        return;
    }
    log_dbg!(
        "[(NSRunLoop*){:?} removePort:{:?} forMode:{:?}]",
        this,
        port,
        mode,
    );
    if !unregister_mode(env, this, port, mode) { return; }
    let maybe_idx = env
        .objc
        .borrow::<NSRunLoopHostObject>(this)
        .ports
        .iter()
        .position(|&p| p == port);
    if let Some(idx) = maybe_idx {
        env.objc.borrow_mut::<NSRunLoopHostObject>(this).ports.remove(idx);
        ns_port::release_port(env, port);
    }
}

- (())addTimer:(id)timer // NSTimer*
       forMode:(NSRunLoopMode)mode {
    let _default_mode = ns_string::get_static_str(env, NSDefaultRunLoopMode);
    let _common_modes = ns_string::get_static_str(env, NSRunLoopCommonModes);
    // TODO: handle other modes
    // assert!(msg![env; mode isEqualToString:default_mode] || msg![env; mode
    // isEqualToString:common_modes]);

    log_dbg!(
        "Adding timer {:?} to run loop {:?} with mode {:?}",
        timer,
        this,
        ns_string::to_rust_string(env, mode),
    );

    register_mode(env, this, timer, mode);

    // FIX: Check if the timer is already in the list. If it is, exit early to
    // prevent duplicate entries and subsequent assertion panics on removal.
    if env.objc.borrow::<NSRunLoopHostObject>(this).timers.contains(&timer) {
        log_dbg!("Timer {:?} is already in run loop {:?}, ignoring duplicate addition.", timer, this);
        return;
    }

    retain(env, timer);

    let host_object = env.objc.borrow_mut::<NSRunLoopHostObject>(this);
    host_object.timers.push(timer);
    ns_timer::set_run_loop(env, timer, this);
}

- (())cancelPerformSelectorsWithTarget:(id)target {
        if target == nil {
            return;
        }

        log_dbg!("NSRunLoop: cancelPerformSelectorsWithTarget: {:?}", target);

        // Клонируем список таймеров, так как вызов invalidate приведет к
        // удалению таймера из списка (через remove_timer), что изменит массив.
        let timers = env.objc.borrow::<NSRunLoopHostObject>(this).timers.clone();

        // Делаем локальный retain всех таймеров, чтобы избежать use-after-free,
        // аналогично тому, как это сделано ниже в функции `run_run_loop`.
        for &timer in &timers {
            retain(env, timer);
        }

        for &timer in &timers {
            // Запрашиваем целевой объект у таймера напрямую через сообщение.
            let timer_target: id = msg![env; timer target];

            // Если цель совпадает, инвалидируем таймер (он сам удалится из run
            // loop)
            if timer_target == target {
                log_dbg!("NSRunLoop: invalidating timer {:?} for target {:?}", timer, target);
                let _: () = msg![env; timer invalidate];
            }

            // Отпускаем локальный retain
            release(env, timer);
        }
}

- (())run {
    run_run_loop(env, this, /* single_iteration: */ false, None);
}

- (())runUntilDate:(id)date {
    let time_limit: NSTimeInterval = msg![env; date timeIntervalSince1970];
    run_run_loop(env, this, /* single_iteration: */ false, Some(time_limit));
}

// TODO: other run methods

@end

};

/// For use by Audio Toolbox.
pub fn add_audio_unit(env: &mut Environment, run_loop: id, unit: AudioUnit) {
    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .audio_units
        .push(unit);
}

/// For use by Audio Toolbox.
pub fn remove_audio_unit(env: &mut Environment, run_loop: id, unit: AudioUnit) -> Result<(), ()> {
    let units = &mut env
        .objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .audio_units;
    if let Some(unit_idx) = units.iter().position(|&item| item == unit) {
        units.remove(unit_idx);
        Ok(())
    } else {
        Err(())
    }
}

/// For use by Audio Toolbox.
/// TODO: Honor the requested callback mode: NewOutput treats explicit modes
/// as common, while NewInput currently ignores the mode argument.
/// TODO: Maybe replace this with a `CFRunLoopObserver` or some other generic
/// mechanism?
pub fn add_audio_queue(
    env: &mut Environment,
    run_loop: id,
    queue: AudioQueueRef,
    independent: bool,
) {
    let state = env.objc.borrow_mut::<NSRunLoopHostObject>(run_loop);
    let queues = if independent {
        &mut state.independent_audio_queues
    } else {
        &mut state.audio_queues
    };
    if !queues.contains(&queue) {
        queues.push(queue);
    }
}

/// For use by Audio Toolbox, for either callback scheduling policy.
pub fn remove_audio_queue(env: &mut Environment, run_loop: id, queue: AudioQueueRef) {
    let state = env.objc.borrow_mut::<NSRunLoopHostObject>(run_loop);
    state.audio_queues.retain(|item| *item != queue);
    state.independent_audio_queues.retain(|item| *item != queue);
}

/// For use by NSTimer so it can remove itself once it's invalidated.
pub(super) fn remove_timer(env: &mut Environment, run_loop: id, timer: id) {
    log_dbg!("Removing timer {:?} from run loop {:?}", timer, run_loop);

    // Честная логика Objective-C: если run_loop равен nil, нам не откуда
    // удалять таймер.
    if run_loop == nil {
        return;
    }

    let state = env.objc.borrow_mut::<NSRunLoopHostObject>(run_loop);
    state.registrations.remove(&timer);
    let timers = &mut state.timers;

    let mut i = 0;
    let mut release_count = 0;
    while i < timers.len() {
        if timers[i] == timer {
            timers.swap_remove(i);
            release_count += 1;
        } else {
            i += 1;
        }
    }

    // Убираем жесткий assert!(release_count == 1);
    // В iOS таймер мог быть отменен до добавления в цикл или отменен дважды.
    // Мы просто делаем release столько раз, сколько реально удалили из массива.
    for _ in 0..release_count {
        release(env, timer);
    }
}

/// Run one paced host UI iteration for the app picker. Guest NS/CF APIs
/// use their own activation and deadline instead.
pub fn run_run_loop_single_iteration(env: &mut Environment, run_loop: id) {
    run_run_loop(env, run_loop, /* single_iteration: */ true, None)
}

/// Run a caller-selected mode until a source is handled or the limit is reached.
/// The return values match CFRunLoopRunResult.
pub(crate) fn run_in_mode(
    env: &mut Environment,
    run_loop: id,
    mode: id,
    unix_time_limit: Option<f64>,
    return_after_source: bool,
) -> RunResult {
    let mode = ns_string::to_rust_string(env, mode).to_string();
    // Common modes are a registration set, not an executable mode.
    if mode == NSRunLoopCommonModes {
        return RunResult::Finished;
    }
    run_loop_impl(
        env,
        run_loop,
        false,
        unix_time_limit,
        &mode,
        return_after_source,
        false,
    )
}

/// UIApplicationMain must keep pumping host events even without a window
/// or any guest sources. Ordinary NS/CF run-loop calls may finish when empty.
pub(crate) fn run_application_main_loop(env: &mut Environment, run_loop: id) {
    loop {
        run_loop_impl(
            env,
            run_loop,
            false,
            None,
            NSDefaultRunLoopMode,
            false,
            true,
        );
    }
}

pub fn run_run_loop(
    env: &mut Environment,
    run_loop: id,
    single_iteration: bool,
    unix_time_limit: Option<f64>,
) {
    run_loop_impl(
        env,
        run_loop,
        single_iteration,
        unix_time_limit,
        NSDefaultRunLoopMode,
        false,
        single_iteration || (env.current_thread == 0 && env.window.is_some()),
    );
}

fn run_loop_impl(
    env: &mut Environment,
    run_loop: id,
    single_iteration: bool,
    unix_time_limit: Option<f64>,
    mode: &str,
    return_after_source: bool,
    keep_alive: bool,
) -> RunResult {
    if !keep_alive && !mode_has_work(env, run_loop, mode) {
        return RunResult::Finished;
    }
    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .activations
        .push(Activation {
            mode: mode.to_string(),
            stopped: false,
        });
    let result = run_loop_body(
        env,
        run_loop,
        single_iteration,
        unix_time_limit,
        mode,
        return_after_source,
        keep_alive,
    );
    env.objc
        .borrow_mut::<NSRunLoopHostObject>(run_loop)
        .activations
        .pop();
    result
}

fn run_loop_body(
    env: &mut Environment,
    run_loop: id,
    single_iteration: bool,
    unix_time_limit: Option<f64>,
    mode: &str,
    return_after_source: bool,
    keep_alive: bool,
) -> RunResult {
    // Temporary vectors used to track things without needing a reference to the
    // environment or to lock the object. Re-used each iteration for efficiency.
    let mut timers_tmp = Vec::new();
    let mut audio_queues_tmp = Vec::new();
    let mut audio_units_tmp = Vec::new();

    fn limit_sleep_time(current: &mut Option<Instant>, new: Option<Instant>) {
        if let Some(new) = new {
            *current = Some(current.map_or(new, |i| i.min(new)));
        }
    }

    let is_main_run_loop = env.current_thread == 0;

    if is_main_run_loop && !single_iteration {
        // Diagnostic: everything the app's UI does — event delivery,
        // composition, timers — is dispatched from this loop. If this line
        // never appears in the log, the app hung before its run loop ever
        // started (e.g. somewhere inside applicationDidFinishLaunching).
        log_once!("Main run loop: now dispatching events, timers and composition");
    }

    loop {
        let mut sleep_until = None;
        let mut handled = false;

        // Commit implicit CATransactions
        // From the CATransaction docs:
        //  "Implicit transactions are created automatically when the layer
        //  tree is modified by a thread without an active transaction and are
        //  committed automatically when the thread’s runloop next iterates."
        ca_transaction::State::commit_implicit_transaction(env);

        // We want to process those only on the main run loop
        if is_main_run_loop && (mode == NSDefaultRunLoopMode || mode == "UITrackingRunLoopMode") {
            let (next_due, delivered) = uikit::handle_events_with_result(env);
            handled |= delivered;
            limit_sleep_time(&mut sleep_until, next_due);

            let force_video_composition = media_player::has_active_video(env);
            let next_due = core_animation::recomposite_if_necessary(env, force_video_composition);
            limit_sleep_time(&mut sleep_until, next_due);
        }

        assert!(timers_tmp.is_empty());
        {
            let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
            timers_tmp.extend(
                state
                    .timers
                    .iter()
                    .copied()
                    .filter(|timer| matches_mode(state, *timer, mode)),
            );
        }
        // Retain the timers in case a timer cancels another timer
        // (which releases it)
        for timer in timers_tmp.iter() {
            retain(env, *timer);
        }

        for timer in timers_tmp.drain(..) {
            let (next_due, fired) = ns_timer::handle_timer(env, timer);
            handled |= fired;
            // Timer deadlines are virtual; audio/UI deadlines remain real.
            let host_due = next_due.map(|due| env.guest_clock.host_deadline(due));
            limit_sleep_time(&mut sleep_until, host_due);
            release(env, timer);
        }

        // TODO: We currently don't properly handle if an audio queue or audio
        // unit gets deleted while inside another queue's handler. Fixing this
        // would be best done by implementing a more general run loop source
        // system that can handle invalidation.
        assert!(audio_queues_tmp.is_empty());
        {
            let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
            if is_common_mode(state, mode) {
                audio_queues_tmp.extend_from_slice(&state.audio_queues);
            }
            if is_main_run_loop {
                audio_queues_tmp.extend_from_slice(&state.independent_audio_queues);
            }
        }

        for audio_queue in audio_queues_tmp.drain(..) {
            handle_audio_queue(env, audio_queue);
        }

        // TODO: not clear if audio units should be processed in the run loop
        assert!(audio_units_tmp.is_empty());
        {
            let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
            if is_main_run_loop {
                audio_units_tmp.extend_from_slice(&state.audio_units);
            }
        }

        for audio_unit in audio_units_tmp.drain(..) {
            render_audio_unit(env, audio_unit);
        }

        // Main-thread requests without an explicit mode use common modes.
        handled |= handle_perform_requests(env, run_loop, mode);
        let mut sources = {
            let state = env.objc.borrow::<NSRunLoopHostObject>(run_loop);
            state
                .sources
                .iter()
                .copied()
                .filter(|source| matches_mode(state, *source, mode))
                .collect::<Vec<_>>()
        };
        sources.sort_by_key(|source| env.objc.borrow::<crate::frameworks::core_foundation::cf_run_loop::CFRunLoopSourceHostObject>(*source).order);
        for source in &sources {
            retain(env, *source);
        }
        for source in sources {
            // A version-0 source is one input event. Leave later signaled
            // sources pending when the caller requested one handled source.
            if handled && return_after_source {
                release(env, source);
                continue;
            }
            if !contains_in_mode(env, run_loop, source, mode) {
                release(env, source);
                continue;
            }
            let call = {
                let state = env.objc.borrow_mut::<crate::frameworks::core_foundation::cf_run_loop::CFRunLoopSourceHostObject>(source);
                if state.valid && state.signaled {
                    state.signaled = false;
                    Some((state.perform, state.info))
                } else {
                    None
                }
            };
            if let Some((perform, info)) = call {
                handled = true;
                if !perform.to_ptr().is_null() {
                    let _: () = perform.call_from_host(env, (info,));
                }
            }
            release(env, source);
        }

        // Process Audio Services completion callbacks. Apple's
        // `AudioServicesAddSystemSoundCompletion` fires its registered
        // routine on the run loop that owned it; touchHLE only models a
        // single run loop, so we poll OpenAL source state once per tick
        // and dispatch finished completions here.
        tick_system_sound_completions(env);

        if is_main_run_loop {
            media_player::handle_players(env);
        }

        // Unfortunately, touchHLE has to poll for certain things repeatedly;
        // it can't just wait until the next event appears.
        //
        // For optimal responsiveness we could poll as often as possible, but
        // this results in 100% usage of a CPU core and excessive energy use.
        // On the other hand, for optimal energy use we could always sleep until
        // the next scheduled event (e.g. the next timer), but this would lead
        // to late handling of unscheduled events (e.g. a finger movement) and
        // events that are scheduled but we can't get the time for currently
        // (audio queue buffer exhaustion).
        //
        // The compromise used here is that we will wait for a 60th of a second,
        // or until the next scheduled event, whichever is sooner. iPhone OS
        // apps can't do more than 60fps so this should be fine.
        // Match CFRunLoop's precedence when more than one exit condition
        // applies: handled input, deadline, stop, then an empty mode.
        if handled && return_after_source {
            return RunResult::HandledSource;
        }
        if let Some(limit) = unix_time_limit {
            let now = env
                .guest_clock
                .system_time()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs_f64();
            if now >= limit {
                return RunResult::TimedOut;
            }
            // Recompute using the guest clock each pass, including speed changes.
            let remaining = Duration::try_from_secs_f64(limit - now).unwrap_or(Duration::MAX);
            if let Some(due) = env.guest_clock.now().checked_add(remaining) {
                limit_sleep_time(&mut sleep_until, Some(env.guest_clock.host_deadline(due)));
            }
        }
        if env
            .objc
            .borrow::<NSRunLoopHostObject>(run_loop)
            .activations
            .last()
            .unwrap()
            .stopped
        {
            return RunResult::Stopped;
        }
        if !keep_alive && !mode_has_work(env, run_loop, mode) {
            return RunResult::Finished;
        }
        let limit = Duration::from_millis(1000 / 60);
        env.sleep(sleep_until.map_or(limit, |i| {
            i.saturating_duration_since(Instant::now()).min(limit)
        }));
        // The host app picker uses a paced UI pump. CFRunLoopRunInMode(0)
        // uses the deadline path above and never sleeps here.
        if single_iteration {
            return RunResult::TimedOut;
        }
    }
}

/// Helper method for `mainRunLoop` and `currentRunLoop` NSThread class methods
pub(crate) fn run_loop_for_thread(env: &mut Environment, this: Class, thread_id: ThreadId) -> id {
    if env.threads[thread_id]
        .thread_local_framework_state
        .foundation
        .ns_run_loop
        .run_loop
        == nil
    {
        let host_object = Box::new(NSRunLoopHostObject {
            selector_objects: VecDeque::new(),
            next_perform_sequence: 0,
            audio_units: Vec::new(),
            audio_queues: Vec::new(),
            independent_audio_queues: Vec::new(),
            timers: Vec::new(),
            sources: Vec::new(),
            ports: Vec::new(),
            registrations: HashMap::new(),
            common_modes: HashSet::new(),
            activations: Vec::new(),
        });
        // TODO: is it OK to allocate static object for all threads,
        // not only main one?
        let new = env
            .objc
            .alloc_static_object(this, host_object, &mut env.mem);
        env.threads[thread_id]
            .thread_local_framework_state
            .foundation
            .ns_run_loop
            .run_loop = new;
    }
    env.threads[thread_id]
        .thread_local_framework_state
        .foundation
        .ns_run_loop
        .run_loop
}

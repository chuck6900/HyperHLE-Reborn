/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

//! `NSURLConnection`.
//!
//! HTTP and HTTPS requests use the host transport when `--allow-network-access`
//! is enabled. Synchronous calls use the timeout-bounded transport directly;
//! asynchronous delegate and block APIs run on a worker and deliver callbacks
//! on the guest run loop. The app-specific fake-success override is retained.

use crate::abi::{CallFromHost, GuestFunction};
use crate::frameworks::foundation::url_loading;
use crate::mem::{guest_size_of, ConstVoidPtr, MutPtr, MutVoidPtr};
use crate::objc::{
    autorelease, id, msg, msg_class, nil, objc_classes, release, retain, ClassExports, HostObject,
    NSZonePtr,
};
use std::sync::mpsc::TryRecvError;
use crate::frameworks::core_foundation::cf_run_loop::{CFRunLoopSourceHostObject, CFRunLoopSourceRef};
use crate::frameworks::foundation::ns_run_loop::{register_mode, unregister_mode, NSRunLoopHostObject, NSRunLoopMode};

fn fake_network_success_enabled() -> bool {
    std::env::var_os("TOUCHHLE_FAKE_NETWORK_SUCCESS").is_some()
}

#[derive(Default)]
struct NSURLConnectionHostObject {
    /// `NSURLRequest *`, retained for the lifetime of the connection.
    request: id,
    /// `id<NSURLConnectionDelegate>`, retained for the lifetime of the connection.
    delegate: id,
    /// `NSOperationQueue *`; callbacks are currently delivered on the guest
    /// run loop, so this is retained for API fidelity but not dispatched to.
    delegate_queue: id,
    /// Copied block for sendAsynchronousRequest:queue:completionHandler:.
    completion_handler: id,
    /// The host worker's result channel. Only polled on the guest thread.
    receiver: Option<url_loading::HttpReceiver>,
    started: bool,
    cancelled: bool,
    finished: bool,

    run_loop: id,
    run_loop_mode: NSRunLoopMode,
}
impl HostObject for NSURLConnectionHostObject {}

fn make_fake_success_data(env: &mut crate::Environment) -> id {
    let body = b"{}";
    let len: u32 = body.len().try_into().unwrap();
    let ptr = env.mem.alloc(len);
    env.mem.bytes_at_mut(ptr.cast(), len).copy_from_slice(body);
    let bytes_ptr = ptr.cast_const().cast_void();
    let data: id = msg_class![env; NSData dataWithBytes:bytes_ptr length:len];
    env.mem.free(ptr.cast());
    data
}

fn make_fake_http_response(env: &mut crate::Environment, request: id) -> id {
    use crate::frameworks::foundation::ns_string::from_rust_string;

    let url: id = if request != nil {
        let req_url: id = msg![env; request URL];
        req_url
    } else {
        nil
    };
    let headers: id = msg_class![env; NSMutableDictionary new];
    autorelease(env, headers);
    let content_type_key = from_rust_string(env, "Content-Type".to_string());
    autorelease(env, content_type_key);
    let content_type_val = from_rust_string(env, "application/json".to_string());
    autorelease(env, content_type_val);
    () = msg![env; headers setObject:content_type_val forKey:content_type_key];
    let content_len_key = from_rust_string(env, "Content-Length".to_string());
    autorelease(env, content_len_key);
    let content_len_val = from_rust_string(env, "2".to_string());
    autorelease(env, content_len_val);
    () = msg![env; headers setObject:content_len_val forKey:content_len_key];
    let version = from_rust_string(env, "HTTP/1.1".to_string());
    autorelease(env, version);
    let response: id = msg_class![env; NSHTTPURLResponse alloc];
    let response: id = msg![env;
        response initWithURL:url
                 statusCode:200
                HTTPVersion:version
               headerFields:headers];
    autorelease(env, response)
}

fn invoke_completion_handler(
    env: &mut crate::Environment,
    handler: id,
    response: id,
    data: id,
    error: id,
) {
    if handler == nil {
        return;
    }
    // Apple Block ABI: word 3 of the block literal is the invoke pointer.
    let invoke_addr: u32 = env.mem.read(handler.cast::<u32>() + 3u32);
    if invoke_addr == 0 {
        log!("Warning: NSURLConnection completion block has a NULL invoke pointer");
        return;
    }
    let invoke = GuestFunction::from_addr_with_thumb_bit(invoke_addr);
    let block_arg: ConstVoidPtr = handler.cast_const().cast();
    let _: () = invoke.call_from_host(env, (block_arg, response, data, error));
}

unsafe impl crate::mem::SafeRead for URLConnectionCallbackData{}
struct URLConnectionCallbackData
{
    connection: id,
    response: id,
    data: id,
    error: id,
    source: id,
}

fn _touchHLE_url_connection_runCallbacks(
    env: &mut crate::Environment,
    info: MutPtr<URLConnectionCallbackData>
) {
    let (delegate, handler, connection, run_loop, mode, response, data, error, source) = {
        let info: URLConnectionCallbackData = env.mem.read(info.cast());
        let connection = env.objc.borrow_mut::<NSURLConnectionHostObject>(info.connection);

        (connection.delegate, connection.completion_handler, connection.run_loop, connection.run_loop_mode, info.connection, info.response, info.data, info.error, info.source)
    };

    if delegate != nil {
        if error != nil {
            () = msg![env; delegate connection:connection didFailWithError:error];
        } else {
            () = msg![env; delegate connection:connection didReceiveResponse:response];
            () = msg![env; delegate connection:connection didReceiveData:data];
            () = msg![env; delegate connectionDidFinishLoading:connection];
        }
    }

    invoke_completion_handler(env, handler, response, data, error);

    release(env, response);
    release(env, data);
    release(env, error);

    let owned_handler = {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(connection);
        std::mem::replace(&mut host.completion_handler, nil)
    };
    release(env, owned_handler);

    env.mem.free(info.cast());

    unregister_mode(env, run_loop, source, mode);
}

static mut run_callbacks_fn_static: Option<GuestFunction> = None;

/// Finish the connection exactly once and deliver the result on the guest
/// thread. The timer which called this method retains the connection through
/// the callbacks, even if the app releases its own reference from a callback.
fn finish_connection(
    env: &mut crate::Environment,
    connection: id,
    response: id,
    data: id,
    error: id,
) {
    let (run_loop, mode) = {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(connection);

        (host.run_loop, host.run_loop_mode)
    };

    let run_callbacks_fn = unsafe {
        match run_callbacks_fn_static {
            Some(f) => f,   // already created, reuse it
            None => {
                let f = env.dyld.create_guest_function(
                    &mut env.mem,
                    "_touchHLE_url_connection_runCallbacks",
                    &(_touchHLE_url_connection_runCallbacks
                        as fn(&mut crate::Environment, MutPtr<URLConnectionCallbackData>) -> ()),
                );
                run_callbacks_fn_static = Some(f);
                f
            }
        }
    };

    if run_loop != nil {
        let ptr: MutPtr<URLConnectionCallbackData> = env.mem.alloc(guest_size_of::<URLConnectionCallbackData>()).cast();

        let host = Box::new(CFRunLoopSourceHostObject {
            version: 0,
            info: ptr.cast(),
            retain: GuestFunction::null_ptr(),
            release: GuestFunction::null_ptr(),
            copy_description: GuestFunction::null_ptr(),
            equal: GuestFunction::null_ptr(),
            hash: GuestFunction::null_ptr(),
            schedule: GuestFunction::null_ptr(),
            cancel: GuestFunction::null_ptr(),
            perform: run_callbacks_fn,
            order: 0,
            valid: true,
            signaled: true,
        });
        let class = env
            .objc
            .get_known_class("_touchHLE_CFRunLoopSource", &mut env.mem);
        let source = env.objc.alloc_object(class, host, &mut env.mem);

        retain(env, response);
        retain(env, data);
        retain(env, error);

        env.mem.write(ptr, URLConnectionCallbackData {
            connection,
            response,
            data,
            error,
            source
        });

        register_mode(env, run_loop, source, mode);
    }
    else {
        let (delegate, handler) = {
            let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(connection);

            (host.delegate, host.completion_handler)
        };

        if delegate != nil {
            if error != nil {
                () = msg![env; delegate connection:connection didFailWithError:error];
            } else {
                () = msg![env; delegate connection:connection didReceiveResponse:response];
                () = msg![env; delegate connection:connection didReceiveData:data];
                () = msg![env; delegate connectionDidFinishLoading:connection];
            }
        }

        invoke_completion_handler(env, handler, response, data, error);

        let owned_handler = {
            let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(connection);
            std::mem::replace(&mut host.completion_handler, nil)
        };
        release(env, owned_handler);
    }
}

fn schedule_connection_poll(env: &mut crate::Environment, connection: id, delay: f64) {
    let selector = env
        .objc
        .register_host_selector("_touchHLE_pollNetwork".to_string(), &mut env.mem);
    () = msg![env; connection performSelector:selector withObject:nil afterDelay:delay];
}

fn start_connection(env: &mut crate::Environment, connection: id) {
    let request = {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(connection);
        if host.started || host.cancelled || host.finished {
            return;
        }
        host.started = true;
        host.request
    };

    if fake_network_success_enabled() {
        let selector = env
            .objc
            .register_host_selector("_touchHLE_deliverSuccess".to_string(), &mut env.mem);
        () = msg![env; connection performSelector:selector withObject:nil afterDelay:0.0_f64];
        return;
    }

    let request_data = url_loading::request_from_objc(env, request, nil, None);
    let receiver = url_loading::send_async(request_data, env.options.network_access);
    env.objc
        .borrow_mut::<NSURLConnectionHostObject>(connection)
        .receiver = Some(receiver);
    schedule_connection_poll(env, connection, 0.05);
}

pub const CLASSES: ClassExports = objc_classes! {

(env, this, _cmd);

@implementation NSURLConnection: NSObject

+ (id)allocWithZone:(NSZonePtr)_zone {
    let host = Box::<NSURLConnectionHostObject>::default();
    env.objc.alloc_object(this, host, &mut env.mem)
}

+ (bool)canHandleRequest:(id)_request {
    // HTTP and HTTPS are supported; connectivity is checked when the request
    // is actually started (and remains controlled by --allow-network-access).
    true
}

// MARK: - Synchronous API

+ (id)sendSynchronousRequest:(id)request
           returningResponse:(MutPtr<id>)response_ptr
                       error:(MutPtr<id>)error_ptr {
    if fake_network_success_enabled() {
        log!("NSURLConnection synchronous request: using app-specific fake JSON response");
        if !response_ptr.is_null() {
            let response = make_fake_http_response(env, request);
            retain(env, response);
            env.mem.write(response_ptr, response);
        }
        return make_fake_success_data(env);
    }

    let result = url_loading::send(
        url_loading::request_from_objc(env, request, nil, None),
        env.options.network_access,
    );
    match result {
        Ok(response) => {
            let (ns_response, data) = url_loading::make_foundation_response(env, &response);
            if !response_ptr.is_null() {
                retain(env, ns_response);
                env.mem.write(response_ptr, ns_response);
            }
            data
        }
        Err(network_error) => {
            if !response_ptr.is_null() {
                env.mem.write(response_ptr, nil);
            }
            if !error_ptr.is_null() {
                let error = url_loading::make_foundation_error(env, &network_error);
                retain(env, error);
                env.mem.write(error_ptr, error);
            }
            nil
        }
    }
}

// MARK: - Block-based asynchronous API

+ (())sendAsynchronousRequest:(id)request
                        queue:(id)queue
            completionHandler:(MutVoidPtr)handler {
    let _ = queue; // callbacks run on the guest run loop for now
    if handler.is_null() {
        return;
    }

    if request == nil {
        let error = url_loading::make_foundation_error(
            env,
            &url_loading::HttpError {
                code: -1000,
                description: "The URL request is nil.".to_string(),
            },
        );
        let handler: id = handler.cast();
        invoke_completion_handler(env, handler, nil, nil, error);
        return;
    }

    let connection: id = msg_class![env; NSURLConnection alloc];
    let connection: id = msg![env;
        connection initWithRequest:request
                          delegate:nil
                  startImmediately:false];
    if connection == nil {
        return;
    }
    let handler_object: id = handler.cast();
    let copied_handler: id = msg![env; handler_object copy];
    env.objc
        .borrow_mut::<NSURLConnectionHostObject>(connection)
        .completion_handler = copied_handler;
    () = msg![env; connection start];
    // `performSelector:afterDelay:` has retained the connection as the timer
    // target. Drop this method's ownership; the connection is released after
    // its result has been delivered.
    release(env, connection);
}

// MARK: - Asynchronous delegate API

+ (id)connectionWithRequest:(id)request delegate:(id)delegate {
    let new: id = msg![env; this alloc];
    let new: id = msg![env; new initWithRequest:request delegate:delegate];
    autorelease(env, new)
}

- (id)initWithRequest:(id)request delegate:(id)delegate {
    msg![env; this initWithRequest:request delegate:delegate startImmediately:true]
}

- (())scheduleInRunLoop:(id)run_loop
             forMode:(NSRunLoopMode)mode {
    if run_loop == nil {
        log!("NSURLConnection scheduleInRunLoop:forMode: nil runLoop — returning nil");
        release(env, this);
        return;
    }
    retain(env, run_loop);
    {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(this);
        host.run_loop = run_loop;
        host.run_loop_mode = mode;
    }
}

- (id)initWithRequest:(id)request
         delegate:(id)delegate
 startImmediately:(bool)start_immediately {
    if request == nil {
        log!("NSURLConnection initWithRequest: nil request — returning nil");
        release(env, this);
        return nil;
    }
    retain(env, request);
    retain(env, delegate);
    {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(this);
        host.request = request;
        host.delegate = delegate;
        host.cancelled = false;
        host.finished = false;
        host.started = false;
    }
    if start_immediately {
        () = msg![env; this start];
    }
    this
}

- (())start {
    start_connection(env, this);
}

// Internal timer callback for the legacy fake-success profile.
- (())_touchHLE_deliverSuccess {
    let request = {
        let host = env.objc.borrow::<NSURLConnectionHostObject>(this);
        if host.cancelled || host.finished {
            return;
        }
        host.request
    };
    log!("NSURLConnection: delivering app-specific fake HTTP 200 success");
    let response = make_fake_http_response(env, request);
    let data = make_fake_success_data(env);
    finish_connection(env, this, response, data, nil);
}

// Polling callback for a real host request. No guest pointers or Objective-C
// objects are ever passed to the background worker.
- (())_touchHLE_pollNetwork {
    let poll = {
        let host = env.objc.borrow::<NSURLConnectionHostObject>(this);
        if host.cancelled || host.finished {
            return;
        }
        let Some(receiver) = host.receiver.as_ref() else {
            return;
        };
        receiver.try_recv()
    };
    match poll {
        Ok(Ok(response)) => {
            let (ns_response, data) = url_loading::make_foundation_response(env, &response);
            finish_connection(env, this, ns_response, data, nil);
        }
        Ok(Err(network_error)) => {
            let error = url_loading::make_foundation_error(env, &network_error);
            finish_connection(env, this, nil, nil, error);
        }
        Err(TryRecvError::Empty) => schedule_connection_poll(env, this, 0.05),
        Err(TryRecvError::Disconnected) => {
            let error = url_loading::make_foundation_error(
                env,
                &url_loading::HttpError {
                    code: -1005,
                    description: "The HTTP worker stopped before returning a result.".to_string(),
                },
            );
            finish_connection(env, this, nil, nil, error);
        }
    }
}

- (())cancel {
    let receiver = {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(this);
        host.cancelled = true;
        host.receiver.take()
    };
    drop(receiver);
}

- (id)originalRequest {
    env.objc.borrow::<NSURLConnectionHostObject>(this).request
}
- (id)currentRequest {
    env.objc.borrow::<NSURLConnectionHostObject>(this).request
}

- (())setDelegateQueue:(id)queue {
    retain(env, queue);
    let old_queue = {
        let host = env.objc.borrow_mut::<NSURLConnectionHostObject>(this);
        std::mem::replace(&mut host.delegate_queue, queue)
    };
    release(env, old_queue);
}

- (id)delegateQueue {
    env.objc.borrow::<NSURLConnectionHostObject>(this).delegate_queue
}

- (())dealloc {
    let (request, delegate, delegate_queue, completion_handler) = {
        let host = env.objc.borrow::<NSURLConnectionHostObject>(this);
        (
            host.request,
            host.delegate,
            host.delegate_queue,
            host.completion_handler,
        )
    };
    release(env, request);
    release(env, delegate);
    release(env, delegate_queue);
    release(env, completion_handler);
    env.objc.dealloc_object(this, &mut env.mem);
}

@end

};

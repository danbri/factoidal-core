use std::ffi::{CStr, CString, c_char, c_void};
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::ptr::NonNull;

use serde_json::Value;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
type NewSession = unsafe extern "C" fn() -> *mut c_void;
type FreeSession = unsafe extern "C" fn(*mut c_void);
type Call =
    unsafe extern "C" fn(*mut c_void, *const c_char, *const c_char, u32, u32) -> *mut c_char;
type FreeAnswer = unsafe extern "C" fn(*mut c_char);

struct Library(NonNull<c_void>);

impl Library {
    fn open(path: &Path) -> Result<Self> {
        let path = CString::new(path.as_os_str().as_bytes())?;
        // SAFETY: the path is NUL-terminated and the handle is owned by Library.
        // The Lean task pool lives for the process. Closing our handle must not
        // unmap its code while a pool thread is still running.
        let flags = libc::RTLD_NOW | libc::RTLD_LOCAL | libc::RTLD_NODELETE;
        let handle = unsafe { libc::dlopen(path.as_ptr(), flags) };
        NonNull::new(handle).map(Self).ok_or_else(loader_error)
    }

    fn symbol(&self, name: &CStr) -> Result<NonNull<c_void>> {
        // SAFETY: the open library handle and symbol name remain valid for the call.
        let address = unsafe { libc::dlsym(self.0.as_ptr(), name.as_ptr()) };
        NonNull::new(address).ok_or_else(loader_error)
    }
}

impl Drop for Library {
    fn drop(&mut self) {
        // SAFETY: all sessions borrow the engine and have ended before the handle closes.
        unsafe { libc::dlclose(self.0.as_ptr()) };
    }
}

fn loader_error() -> Box<dyn std::error::Error> {
    // SAFETY: dlerror returns either null or a NUL-terminated message. Copy it immediately.
    let error = unsafe { libc::dlerror() };
    if error.is_null() {
        return "native engine loader returned a null pointer".into();
    }
    unsafe { CStr::from_ptr(error) }
        .to_string_lossy()
        .into_owned()
        .into()
}

pub struct Engine {
    _library: Library,
    new_session: NewSession,
    free_session: FreeSession,
    call: Call,
    free_answer: FreeAnswer,
}

impl Engine {
    pub fn open(library: &Path) -> Result<Self> {
        let library = Library::open(library)?;
        // SAFETY: these symbols have the signatures declared in web_render_shim.c.
        // The caller supplies the trusted Foafnaut native engine build.
        unsafe {
            Ok(Self {
                new_session: std::mem::transmute::<*mut c_void, NewSession>(
                    library.symbol(c"web_session_new")?.as_ptr(),
                ),
                free_session: std::mem::transmute::<*mut c_void, FreeSession>(
                    library.symbol(c"web_session_free")?.as_ptr(),
                ),
                call: std::mem::transmute::<*mut c_void, Call>(
                    library.symbol(c"web_session_call")?.as_ptr(),
                ),
                free_answer: std::mem::transmute::<*mut c_void, FreeAnswer>(
                    library.symbol(c"web_render_free")?.as_ptr(),
                ),
                _library: library,
            })
        }
    }

    pub fn session(&self) -> Result<Session<'_>> {
        // SAFETY: the engine is loaded and the returned pointer is owned by Session.
        let handle = NonNull::new(unsafe { (self.new_session)() })
            .ok_or("the native engine could not create a session")?;
        Ok(Session {
            engine: self,
            handle,
        })
    }
}

pub struct Session<'a> {
    engine: &'a Engine,
    handle: NonNull<c_void>,
}

impl Session<'_> {
    pub fn call(&mut self, html: &str, request: &Value, size: [u32; 2]) -> Result<Value> {
        let html = CString::new(html)?;
        let request = CString::new(serde_json::to_vec(request)?)?;
        // SAFETY: this session is live and exclusively borrowed. Both strings remain
        // NUL-terminated and live throughout the call.
        let result = unsafe {
            (self.engine.call)(
                self.handle.as_ptr(),
                html.as_ptr(),
                request.as_ptr(),
                size[0],
                size[1],
            )
        };
        let result = NonNull::new(result).ok_or("the native engine returned no answer")?;
        // SAFETY: the engine returns an owned, NUL-terminated string. Decode to an
        // owned result, then free the C allocation even when decoding fails.
        let decoded =
            unsafe { serde_json::from_slice::<Value>(CStr::from_ptr(result.as_ptr()).to_bytes()) };
        unsafe { (self.engine.free_answer)(result.as_ptr()) };
        let decoded = decoded?;
        if let Some(message) = decoded["error"].as_str() {
            return Err(message.to_owned().into());
        }
        Ok(decoded)
    }
}

impl Drop for Session<'_> {
    fn drop(&mut self) {
        // SAFETY: this is the only owner of the session and the engine is still loaded.
        unsafe { (self.engine.free_session)(self.handle.as_ptr()) };
    }
}

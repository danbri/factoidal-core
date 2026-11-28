use std::ffi::{c_char, c_void};
use std::path::Path;
use std::ptr::NonNull;
use std::time::Duration;

use raw_window_handle::{RawDisplayHandle, RawWindowHandle};

use crate::engine::Library;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[repr(C)]
#[derive(Default)]
pub struct Event {
    pub kind: u32,
    pub a: i32,
    pub b: i32,
    pub time: u32,
    pub flags: u32,
}

pub struct Window {
    _library: Library,
    display: RawDisplayHandle,
    window: RawWindowHandle,
    pump: unsafe extern "C" fn(),
    next: unsafe extern "C" fn(*mut Event) -> i32,
    wait: unsafe extern "C" fn(f64) -> i32,
    show: unsafe extern "C" fn(),
    hide: unsafe extern "C" fn(),
}

impl Window {
    pub fn open(path: &Path, size: [u32; 2]) -> Result<Self> {
        let library = Library::open(path)?;
        // SAFETY: these signatures are the window bridge's ABI. The library
        // stays open while its handles and function pointers are in use.
        macro_rules! function {
            ($name:literal, $signature:ty) => {{
                let address = library.symbol($name)?;
                unsafe { std::mem::transmute::<*mut c_void, $signature>(address.as_ptr()) }
            }};
        }
        let event_size = function!(c"ng_event_size", unsafe extern "C" fn() -> u32);
        if usize::try_from(unsafe { event_size() })? != std::mem::size_of::<Event>() {
            return Err("unsupported native window event ABI".into());
        }

        let create = function!(c"ng_create", unsafe extern "C" fn(u32, u32) -> *mut c_void);
        let set_title = function!(c"ng_set_title", unsafe extern "C" fn(*const c_char));
        let pump = function!(c"ng_pump", unsafe extern "C" fn());
        let next = function!(c"ng_next_event", unsafe extern "C" fn(*mut Event) -> i32);
        let wait = function!(c"ng_wait_event", unsafe extern "C" fn(f64) -> i32);
        let show = function!(c"ng_show_after_surface", unsafe extern "C" fn());
        let hide = function!(c"ng_hide", unsafe extern "C" fn());
        #[cfg(target_os = "linux")]
        let surface_system = function!(c"ng_surface_system", unsafe extern "C" fn() -> i32);
        #[cfg(target_os = "linux")]
        let window_handle = function!(c"ng_window_handle", unsafe extern "C" fn() -> *mut c_void);

        // SAFETY: called from main. Both bridges require their main thread and
        // return null if a native window could not be created.
        let handle = NonNull::new(unsafe { create(size[0], size[1]) })
            .ok_or("could not open the native window")?;
        unsafe { set_title(c"Foafnaut".as_ptr()) };

        #[cfg(target_os = "macos")]
        let (display, window) = (
            raw_window_handle::AppKitDisplayHandle::new().into(),
            raw_window_handle::AppKitWindowHandle::new(handle).into(),
        );
        #[cfg(target_os = "linux")]
        let (display, window) = {
            let window =
                NonNull::new(unsafe { window_handle() }).ok_or("missing Linux window handle")?;
            match unsafe { surface_system() } {
                1 => (
                    raw_window_handle::XlibDisplayHandle::new(Some(handle), 0).into(),
                    raw_window_handle::XlibWindowHandle::new(window.as_ptr() as libc::c_ulong)
                        .into(),
                ),
                2 => (
                    raw_window_handle::WaylandDisplayHandle::new(handle).into(),
                    raw_window_handle::WaylandWindowHandle::new(window).into(),
                ),
                _ => return Err("unsupported Linux window system".into()),
            }
        };

        Ok(Self {
            _library: library,
            display,
            window,
            pump,
            next,
            wait,
            show,
            hide,
        })
    }

    pub fn surface(&self, instance: &wgpu::Instance) -> Result<wgpu::Surface<'_>> {
        // SAFETY: the existing bridges retain the native handles. The surface
        // borrows this Window and is dropped before the window is hidden.
        let surface = unsafe {
            instance.create_surface_unsafe(wgpu::SurfaceTargetUnsafe::RawHandle {
                raw_display_handle: self.display,
                raw_window_handle: self.window,
            })
        }?;
        Ok(surface)
    }

    pub fn show(&self) {
        // SAFETY: all window calls are made on main while the library is live.
        unsafe { (self.show)() };
    }

    pub fn wait_and_pump(&self, max_wait: Duration) {
        // SAFETY: all window calls are made on main while the library is live.
        unsafe {
            (self.wait)(max_wait.as_secs_f64() * 1000.0);
            (self.pump)();
        }
    }

    pub fn next(&self) -> Option<Event> {
        let mut event = Event::default();
        // SAFETY: the bridge's event size was checked at construction.
        (unsafe { (self.next)(&mut event) } == 1).then_some(event)
    }
}

impl Drop for Window {
    fn drop(&mut self) {
        // SAFETY: the borrowed surface has been dropped and the library is live.
        unsafe { (self.hide)() };
    }
}

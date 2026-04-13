#![windows_subsystem = "windows"]

use ddc_hi::{Ddc, Display};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, Mutex};
use std::{thread, time::Duration};

use windows::core::PCWSTR;
use windows::Win32::Foundation::{
    BOOL, ERROR_ALREADY_EXISTS, GetLastError, HWND, LPARAM, LRESULT, POINT, RECT, WPARAM,
};
use windows::Win32::Graphics::Gdi::{
    EnumDisplayDevicesW, EnumDisplayMonitors, GetMonitorInfoW, MonitorFromWindow,
    DISPLAY_DEVICEW, HDC, HMONITOR, MONITORINFO, MONITORINFOEXW,
    MONITOR_DEFAULTTONEAREST,
};
use windows::Win32::UI::Accessibility::{SetWinEventHook, HWINEVENTHOOK};
#[cfg(debug_assertions)]
use windows::Win32::UI::Input::KeyboardAndMouse::{RegisterHotKey, MOD_CONTROL, MOD_ALT};
use windows::Win32::UI::Shell::{
    Shell_NotifyIconW, NIF_ICON, NIF_MESSAGE, NIF_TIP, NIM_ADD, NIM_DELETE, NOTIFYICONDATAW,
};
use windows::Win32::UI::WindowsAndMessaging::{
    AppendMenuW, CallNextHookEx, CreatePopupMenu, CreateWindowExW, DefWindowProcW,
    DispatchMessageW, EnumWindows, GetClassNameW, GetCursorPos, GetMessageW, GetWindowRect,
    IsIconic, IsWindow, IsWindowVisible, LoadIconW, PostQuitMessage, RegisterClassW,
    SetCursorPos, SetForegroundWindow, SetWindowPos, SetWindowsHookExW, TrackPopupMenu,
    TranslateMessage, CS_HREDRAW, CS_VREDRAW, CW_USEDEFAULT, EVENT_OBJECT_SHOW, HWND_TOP,
    MF_STRING, MSG, MSLLHOOKSTRUCT, OBJID_WINDOW, SWP_NOSIZE, SWP_NOZORDER,
    TPM_BOTTOMALIGN, TPM_LEFTALIGN, WH_MOUSE_LL, WM_COMMAND, WM_DESTROY,
    WM_LBUTTONUP, WM_QUIT, WM_RBUTTONUP, WM_USER, WNDCLASSW, WS_OVERLAPPEDWINDOW,
    WINEVENT_OUTOFCONTEXT, EVENT_SYSTEM_MINIMIZEEND, GetWindowPlacement, SetWindowPlacement,
    WINDOWPLACEMENT, EVENT_SYSTEM_MOVESIZESTART, EVENT_SYSTEM_MOVESIZEEND,
    EVENT_OBJECT_LOCATIONCHANGE, KillTimer, SetTimer, WM_TIMER, WINDOW_EX_STYLE,
};
#[cfg(debug_assertions)]
use windows::Win32::UI::WindowsAndMessaging::WM_HOTKEY;

use windows::Win32::System::Threading::CreateMutexW;

// ─── Constants ───────────────────────────────────────────────────────

/// Number of consecutive identical DDC readings before we act (× 2s poll = 6s)
const DEBOUNCE_THRESHOLD: u32 = 3;
/// Window move delay to avoid crashing fragile apps (like Blender render window)
const SNAP_DELAY_MS: u32 = 150;
const TIMER_DELAY_MOVE: usize = 100;

// ─── Types ───────────────────────────────────────────────────────────

#[derive(Clone, PartialEq, Debug)]
enum PowerState {
    On,
    Off,
}

/// Per-monitor debounce tracking
struct MonitorDebounce {
    confirmed_state: PowerState,
    pending_state: PowerState,
    count: u32,
}

/// Adapter ↔ child‐monitor PnP mapping from EnumDisplayDevicesW
struct AdapterMonitorInfo {
    adapter_name: String, // \\.\DISPLAY1
    pnp_id: String,       // e.g. "DEL40F3"
}

/// A non-primary monitor that can be toggled via hotkey.
struct ToggleableMonitor {
    device_name: String,
    #[allow(dead_code)] // Only read in debug builds for printout
    rect: RECT,
    is_disabled: bool,
}

/// (raw HWND handle, original window RECT) — for saving/restoring window positions.
type WindowRecord = (isize, RECT);

/// Map of device_name → list of saved window positions.
type SavedWindowsMap = HashMap<String, Vec<WindowRecord>>;

// ─── Global state ────────────────────────────────────────────────────

/// Whether the program is still running. Set to false via the tray menu.
static RUNNING: AtomicBool = AtomicBool::new(true);

/// Windows currently being moved or resized by the user.
/// We ignore these in LOCATIONCHANGE to allow smooth dragging.
static MOVING_WINDOWS: LazyLock<Mutex<HashSet<isize>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

/// Windows that appeared recently and are waiting for a safety delay before snapping.
static PENDING_MOVES: Mutex<VecDeque<isize>> = Mutex::new(VecDeque::new());

/// Screen rectangles where the cursor is blocked from entering.
/// Updated by the main thread and hotkey handler, read by the hook callback.
static BLOCKED_RECTS: Mutex<Vec<RECT>> = Mutex::new(Vec::new());

/// Non-primary monitors available for hotkey toggling.
/// Populated at startup, toggled by the hook thread's hotkey handler.
static TOGGLEABLE_MONITORS: Mutex<Vec<ToggleableMonitor>> = Mutex::new(Vec::new());

/// Original positions of windows that were moved off a disabled monitor.
/// Key: device_name (\\.\.DISPLAYn), Value: list of (HWND raw handle, original RECT).
/// Used to restore windows when the monitor is re-enabled.
static SAVED_WINDOWS: LazyLock<Mutex<SavedWindowsMap>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

// ─── Helpers ─────────────────────────────────────────────────────────

fn decode_power(v: u16) -> PowerState {
    match v {
        0x01 => PowerState::On,
        _ => PowerState::Off,
    }
}

fn wide(s: &str) -> Vec<u16> {
    s.encode_utf16().chain(Some(0)).collect()
}

fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    format!("{:x}", hasher.finalize())
}

/// Convert a fixed-size wide‐char buffer to a Rust String (up to the first null).
fn wchar_to_string(buf: &[u16]) -> String {
    let len = buf.iter().position(|&c| c == 0).unwrap_or(buf.len());
    String::from_utf16_lossy(&buf[..len])
}

fn point_in_rect(pt: &POINT, r: &RECT) -> bool {
    pt.x >= r.left && pt.x < r.right && pt.y >= r.top && pt.y < r.bottom
}

fn rects_equal(a: &RECT, b: &RECT) -> bool {
    a.left == b.left && a.top == b.top && a.right == b.right && a.bottom == b.bottom
}

// ─── 1. EDID → Device Mapping ──────────────────────────────────────

/// Enumerate all display adapters and their child monitors via two-level
/// `EnumDisplayDevicesW`. Returns (adapter_name, pnp_id) pairs.
fn enumerate_adapter_monitors() -> Vec<AdapterMonitorInfo> {
    let mut results = Vec::new();

    unsafe {
        let mut adapter_idx: u32 = 0;
        loop {
            let mut adapter: DISPLAY_DEVICEW = std::mem::zeroed();
            adapter.cb = std::mem::size_of::<DISPLAY_DEVICEW>() as u32;

            if !EnumDisplayDevicesW(PCWSTR::null(), adapter_idx, &mut adapter, 0).as_bool() {
                break;
            }

            let adapter_name = wchar_to_string(&adapter.DeviceName);

            // Enumerate child monitors attached to this adapter
            let mut mon_idx: u32 = 0;
            loop {
                let mut monitor: DISPLAY_DEVICEW = std::mem::zeroed();
                monitor.cb = std::mem::size_of::<DISPLAY_DEVICEW>() as u32;

                let adapter_name_wide = wide(&adapter_name);
                if !EnumDisplayDevicesW(
                    PCWSTR(adapter_name_wide.as_ptr()),
                    mon_idx,
                    &mut monitor,
                    0,
                )
                .as_bool()
                {
                    break;
                }

                // DeviceID looks like "MONITOR\DEL40F3\{guid}\0000"
                // Extract the PnP hardware ID (second segment).
                let device_id = wchar_to_string(&monitor.DeviceID);
                if let Some(pnp_id) = device_id.split('\\').nth(1) {
                    results.push(AdapterMonitorInfo {
                        adapter_name: adapter_name.clone(),
                        pnp_id: pnp_id.to_uppercase(),
                    });
                }

                mon_idx += 1;
            }

            adapter_idx += 1;
        }
    }

    results
}

/// Match a ddc-hi display to its Windows adapter name via manufacturer_id + model_id.
fn match_display_to_device(
    info: &ddc_hi::DisplayInfo,
    adapters: &[AdapterMonitorInfo],
) -> Option<String> {
    let mfr = info.manufacturer_id.as_deref()?;
    let model = info.model_id?;
    let expected = format!("{}{:04X}", mfr, model).to_uppercase();

    adapters
        .iter()
        .find(|a| a.pnp_id == expected)
        .map(|a| a.adapter_name.clone())
}

// ─── 2. Monitor Rect Lookup ────────────────────────────────────────

/// Collect all (HMONITOR, device_name, RECT) tuples.
fn get_all_monitors() -> Vec<(HMONITOR, String, RECT)> {
    let mut monitors: Vec<(HMONITOR, String, RECT)> = Vec::new();

    unsafe extern "system" fn callback(
        hmonitor: HMONITOR,
        _hdc: HDC,
        _lprect: *mut RECT,
        lparam: LPARAM,
    ) -> BOOL {
        let list = &mut *(lparam.0 as *mut Vec<(HMONITOR, String, RECT)>);

        let mut info: MONITORINFOEXW = std::mem::zeroed();
        info.monitorInfo.cbSize = std::mem::size_of::<MONITORINFOEXW>() as u32;

        if GetMonitorInfoW(hmonitor, &mut info.monitorInfo as *mut MONITORINFO).as_bool() {
            let name = wchar_to_string(&info.szDevice);
            let rect = info.monitorInfo.rcMonitor;
            list.push((hmonitor, name, rect));
        }

        BOOL(1) // continue enumeration
    }

    unsafe {
        let _ = EnumDisplayMonitors(
            HDC::default(),
            None,
            Some(callback),
            LPARAM(&mut monitors as *mut _ as isize),
        );
    }

    monitors
}

/// Get the screen RECT for a given \\.\DISPLAYn device name.
fn get_monitor_rect(device_name: &str) -> Option<RECT> {
    get_all_monitors()
        .into_iter()
        .find(|(_, name, _)| name == device_name)
        .map(|(_, _, rect)| rect)
}

/// Get the RECT of the primary (or any other active) monitor to move windows to.
/// Excludes the given disabled_rect.
fn get_fallback_monitor_rect(disabled_rect: &RECT) -> Option<RECT> {
    get_all_monitors()
        .into_iter()
        .find(|(_, _, rect)| rect != disabled_rect)
        .map(|(_, _, rect)| rect)
}

// ─── 3. Window Migration ───────────────────────────────────────────

/// Check if a window is a system/shell window that should not be moved.
unsafe fn is_system_window(hwnd: HWND) -> bool {
    let mut class_buf = [0u16; 64];
    let class_len = GetClassNameW(hwnd, &mut class_buf);
    if class_len > 0 {
        let class_name = String::from_utf16_lossy(&class_buf[..class_len as usize]);
        match class_name.as_str() {
            "Shell_TrayWnd"            // Main taskbar
            | "Shell_SecondaryTrayWnd" // Secondary taskbar
            | "Progman"                // Desktop
            | "WorkerW"                // Desktop worker
            => return true,
            _ => {}
        }
    }
    false
}

/// If the given window is on a blocked monitor, move it to a fallback one.
fn move_single_window_if_blocked(hwnd: HWND) {
    unsafe {
        // Skip invisible or system windows. Don't skip iconic (minimized) windows.
        if !IsWindowVisible(hwnd).as_bool() || is_system_window(hwnd) {
            return;
        }

        let hmon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
        let mut minfo: MONITORINFOEXW = std::mem::zeroed();
        minfo.monitorInfo.cbSize = std::mem::size_of::<MONITORINFOEXW>() as u32;

        if !GetMonitorInfoW(hmon, &mut minfo.monitorInfo as *mut MONITORINFO).as_bool() {
            return;
        }

        let mon_rect = minfo.monitorInfo.rcMonitor;
        let blocked = {
            let rects = BLOCKED_RECTS.lock().unwrap();
            rects.iter().any(|r| rects_equal(r, &mon_rect))
        };

        if blocked {
            if let Some(fallback) = get_fallback_monitor_rect(&mon_rect) {
                let dx = fallback.left - mon_rect.left;
                let dy = fallback.top - mon_rect.top;

                if IsIconic(hwnd).as_bool() {
                    let mut wp: WINDOWPLACEMENT = std::mem::zeroed();
                    wp.length = std::mem::size_of::<WINDOWPLACEMENT>() as u32;
                    if GetWindowPlacement(hwnd, &mut wp).is_ok() {
                        wp.rcNormalPosition.left += dx;
                        wp.rcNormalPosition.right += dx;
                        wp.rcNormalPosition.top += dy;
                        wp.rcNormalPosition.bottom += dy;
                        let _ = SetWindowPlacement(hwnd, &wp);
                    }
                } else {
                    let mut wrect: RECT = std::mem::zeroed();
                    if GetWindowRect(hwnd, &mut wrect).is_ok() {
                        let _ = SetWindowPos(
                            hwnd,
                            HWND_TOP,
                            wrect.left + dx,
                            wrect.top + dy,
                            0,
                            0,
                            SWP_NOSIZE | SWP_NOZORDER,
                        );
                    }
                }
            }
        }
    }
}

/// Move all visible top-level windows off the disabled monitor to a fallback one.
/// Saves their original positions for later restoration.
fn move_windows_off_monitor(disabled_rect: &RECT, device_name: &str) {
    let fallback = match get_fallback_monitor_rect(disabled_rect) {
        Some(r) => r,
        None => {
            println!("  No fallback monitor to move windows to");
            return;
        }
    };

    // Offset to translate from disabled monitor coords to fallback monitor coords
    let dx = fallback.left - disabled_rect.left;
    let dy = fallback.top - disabled_rect.top;

    // Collect moved windows: (hwnd_raw, original_rect)
    let moved: Mutex<Vec<WindowRecord>> = Mutex::new(Vec::new());

    unsafe extern "system" fn enum_callback(hwnd: HWND, lparam: LPARAM) -> BOOL {
        let (disabled_rect, dx, dy, moved) =
            unsafe { &*(lparam.0 as *const (&RECT, i32, i32, &Mutex<Vec<WindowRecord>>)) };

        unsafe {
            // Skip invisible or system windows. Don't skip iconic (minimized).
            if !IsWindowVisible(hwnd).as_bool() || is_system_window(hwnd) {
                return BOOL(1);
            }

            let mut wrect: RECT = std::mem::zeroed();
            if GetWindowRect(hwnd, &mut wrect).is_err() {
                return BOOL(1);
            }

            // Check which monitor this window is primarily on
            let hmon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
            let mut minfo: MONITORINFOEXW = std::mem::zeroed();
            minfo.monitorInfo.cbSize = std::mem::size_of::<MONITORINFOEXW>() as u32;

            if !GetMonitorInfoW(hmon, &mut minfo.monitorInfo as *mut MONITORINFO).as_bool() {
                return BOOL(1);
            }

            let mon_rect = minfo.monitorInfo.rcMonitor;
            if rects_equal(&mon_rect, disabled_rect) {
                // Save original position
                let mut wrect: RECT = std::mem::zeroed();
                let _ = GetWindowRect(hwnd, &mut wrect);
                moved.lock().unwrap().push((hwnd.0 as isize, wrect));

                if IsIconic(hwnd).as_bool() {
                    let mut wp: WINDOWPLACEMENT = std::mem::zeroed();
                    wp.length = std::mem::size_of::<WINDOWPLACEMENT>() as u32;
                    if GetWindowPlacement(hwnd, &mut wp).is_ok() {
                        wp.rcNormalPosition.left += dx;
                        wp.rcNormalPosition.right += dx;
                        wp.rcNormalPosition.top += dy;
                        wp.rcNormalPosition.bottom += dy;
                        let _ = SetWindowPlacement(hwnd, &wp);
                    }
                } else {
                    let mut wrect: RECT = std::mem::zeroed();
                    if GetWindowRect(hwnd, &mut wrect).is_ok() {
                        let _ = SetWindowPos(
                            hwnd,
                            HWND_TOP,
                            wrect.left + dx,
                            wrect.top + dy,
                            0,
                            0,
                            SWP_NOSIZE | SWP_NOZORDER,
                        );
                    }
                }
            }
        }

        BOOL(1) // continue enumeration
    }

    let context: (&RECT, i32, i32, &Mutex<Vec<WindowRecord>>) =
        (disabled_rect, dx, dy, &moved);

    unsafe {
        let _ = EnumWindows(
            Some(enum_callback),
            LPARAM(&context as *const _ as isize),
        );
    }

    // Also warp the cursor if it's on the disabled monitor
    unsafe {
        let mut pt: POINT = std::mem::zeroed();
        if GetCursorPos(&mut pt).is_ok() && point_in_rect(&pt, disabled_rect) {
            // Determine a safe spot on the fallback monitor (e.g., center)
            let center_x = fallback.left + (fallback.right - fallback.left) / 2;
            let center_y = fallback.top + (fallback.bottom - fallback.top) / 2;
            let _ = SetCursorPos(center_x, center_y);
            println!("  Warped cursor to fallback monitor");
        }
    }

    // Store saved positions for later restoration
    let moved_windows = moved.into_inner().unwrap();
    if !moved_windows.is_empty() {
        println!("  Saved {} window position(s) for restoration", moved_windows.len());
        SAVED_WINDOWS
            .lock()
            .unwrap()
            .insert(device_name.to_string(), moved_windows);
    }
}

/// Restore previously-moved windows back to their original positions.
fn restore_windows_to_monitor(device_name: &str) {
    let saved = SAVED_WINDOWS.lock().unwrap().remove(device_name);
    if let Some(windows) = saved {
        let mut restored = 0;
        for (hwnd_raw, rect) in &windows {
            unsafe {
                let hwnd = HWND(*hwnd_raw as *mut _);
                // Only restore windows that still exist
                if IsWindow(hwnd).as_bool() {
                    let _ = SetWindowPos(
                        hwnd,
                        HWND_TOP,
                        rect.left,
                        rect.top,
                        0,
                        0,
                        SWP_NOSIZE | SWP_NOZORDER,
                    );
                    restored += 1;
                }
            }
        }
        if restored > 0 {
            println!("  Restored {} window(s) to {}", restored, device_name);
        }
    }
}

// ─── 4. Low-Level Hooks, Hotkeys & Tray ──────────────────────────────

const WM_TRAY_ICON: u32 = WM_USER + 1;
const ID_TRAY_EXIT: usize = 1001;

/// TrayManager handles the hidden window and its associated tray icon.
/// Reference to the tray's message window so other threads can set timers on it.
static TRAY_HWND: std::sync::atomic::AtomicIsize = std::sync::atomic::AtomicIsize::new(0);

struct TrayManager {
    hwnd: HWND,
}

impl TrayManager {
    fn new() -> Self {
        unsafe {
            let instance = windows::Win32::System::LibraryLoader::GetModuleHandleW(None).unwrap();
            let class_name = PCWSTR("DDC_CHECK_TRAY\0".encode_utf16().collect::<Vec<_>>().as_ptr());

            let wc = WNDCLASSW {
                lpfnWndProc: Some(tray_wnd_proc),
                hInstance: instance.into(),
                lpszClassName: class_name,
                style: CS_HREDRAW | CS_VREDRAW,
                ..Default::default()
            };

            RegisterClassW(&wc);

            let hwnd = CreateWindowExW(
                WINDOW_EX_STYLE::default(),
                class_name,
                PCWSTR("DDC Tray Window\0".encode_utf16().collect::<Vec<_>>().as_ptr()),
                WS_OVERLAPPEDWINDOW,
                CW_USEDEFAULT,
                CW_USEDEFAULT,
                CW_USEDEFAULT,
                CW_USEDEFAULT,
                None,
                None,
                instance,
                None,
            ).unwrap();

            TRAY_HWND.store(hwnd.0 as isize, Ordering::SeqCst);

            let mut nid = NOTIFYICONDATAW {
                cbSize: std::mem::size_of::<NOTIFYICONDATAW>() as u32,
                hWnd: hwnd,
                uID: 1,
                uFlags: NIF_ICON | NIF_MESSAGE | NIF_TIP,
                uCallbackMessage: WM_TRAY_ICON,
                hIcon: LoadIconW(instance, PCWSTR(std::ptr::without_provenance(1))).unwrap(),
                ..Default::default()
            };

            // Set tooltip
            let tooltip = "Monitor Manager\0".encode_utf16().collect::<Vec<_>>();
            nid.szTip[..tooltip.len()].copy_from_slice(&tooltip);

            let _ = Shell_NotifyIconW(NIM_ADD, &nid);

            Self { hwnd }
        }
    }
}

impl Drop for TrayManager {
    fn drop(&mut self) {
        unsafe {
            let nid = NOTIFYICONDATAW {
                cbSize: std::mem::size_of::<NOTIFYICONDATAW>() as u32,
                hWnd: self.hwnd,
                uID: 1,
                ..Default::default()
            };
            let _ = Shell_NotifyIconW(NIM_DELETE, &nid);
        }
    }
}

unsafe extern "system" fn tray_wnd_proc(
    hwnd: HWND,
    msg: u32,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    match msg {
        WM_TRAY_ICON => {
            let event = lparam.0 as u32;
            if event == WM_RBUTTONUP || event == WM_LBUTTONUP {
                let mut pt = POINT::default();
                let _ = GetCursorPos(&mut pt);

                let h_menu = CreatePopupMenu().unwrap();
                let _ = AppendMenuW(h_menu, MF_STRING, ID_TRAY_EXIT, PCWSTR("Exit\0".encode_utf16().collect::<Vec<_>>().as_ptr()));

                // Required for TrackPopupMenu to work correctly with tray icons
                let _ = SetForegroundWindow(hwnd);
                let _ = TrackPopupMenu(
                    h_menu,
                    TPM_LEFTALIGN | TPM_BOTTOMALIGN,
                    pt.x,
                    pt.y,
                    0,
                    hwnd,
                    None,
                );
            }
            LRESULT(0)
        }
        WM_COMMAND => {
            if lparam.0 == 0 && (wparam.0 & 0xffff) == ID_TRAY_EXIT {
                RUNNING.store(false, Ordering::SeqCst);
                PostQuitMessage(0);
            }
            LRESULT(0)
        }
        WM_TIMER => {
            if wparam.0 == TIMER_DELAY_MOVE {
                // Drain the queue of pending moves
                let mut handles = Vec::new();
                {
                    let mut pending = PENDING_MOVES.lock().unwrap();
                    while let Some(hwnd_raw) = pending.pop_front() {
                        handles.push(HWND(hwnd_raw as *mut _));
                    }
                }

                // If no more pending moves, kill the timer to save resources
                if handles.is_empty() {
                    let _ = KillTimer(hwnd, TIMER_DELAY_MOVE);
                }

                for h in handles {
                    move_single_window_if_blocked(h);
                }
            }
            LRESULT(0)
        }
        WM_DESTROY => {
            PostQuitMessage(0);
            LRESULT(0)
        }
        _ => DefWindowProcW(hwnd, msg, wparam, lparam),
    }
}

/// Low-level mouse hook to block the cursor from entering ghost monitor regions.
unsafe extern "system" fn mouse_hook_proc(
    code: i32,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    if code >= 0 {
        let info = &*(lparam.0 as *const MSLLHOOKSTRUCT);
        if let Ok(rects) = BLOCKED_RECTS.lock() {
            for rect in rects.iter() {
                if point_in_rect(&info.pt, rect) {
                    return LRESULT(1); // Block — cursor stays at previous position
                }
            }
        }
    }
    CallNextHookEx(None, code, wparam, lparam)
}

/// WinEventHook callback to catch windows spawning or moving into blocked monitors.
unsafe extern "system" fn win_event_proc(
    _h_win_event_hook: HWINEVENTHOOK,
    event: u32,
    hwnd: HWND,
    id_object: i32,
    _id_child: i32,
    _dw_event_thread: u32,
    _dwms_event_time: u32,
) {
    if id_object != OBJID_WINDOW.0 {
        return;
    }

    match event {
        EVENT_SYSTEM_MOVESIZESTART => {
            let mut moving = MOVING_WINDOWS.lock().unwrap();
            moving.insert(hwnd.0 as isize);
        }
        EVENT_SYSTEM_MOVESIZEEND => {
            {
                let mut moving = MOVING_WINDOWS.lock().unwrap();
                moving.remove(&(hwnd.0 as isize));
            }
            // Now that the user let go, check if it landed in a blocked area
            move_single_window_if_blocked(hwnd);
        }
        EVENT_OBJECT_LOCATIONCHANGE => {
            let is_moving = {
                let moving = MOVING_WINDOWS.lock().unwrap();
                moving.contains(&(hwnd.0 as isize))
            };
            // Only snap if the user isn't actively dragging it (catches minimizing/programmatic moves)
            if !is_moving {
                move_single_window_if_blocked(hwnd);
            }
        }
        EVENT_OBJECT_SHOW | EVENT_SYSTEM_MINIMIZEEND => {
                // Fragile windows (Blender) crash if moved too fast during creation. 
                // We queue them with a safety delay.
                {
                    let mut pending = PENDING_MOVES.lock().unwrap();
                    pending.push_back(hwnd.0 as isize);
                }
                
                // Get the tray window to set a timer on its thread
                let tray_hwnd = TRAY_HWND.load(Ordering::SeqCst);
                if tray_hwnd != 0 {
                    unsafe {
                        let _ = SetTimer(HWND(tray_hwnd as *mut _), TIMER_DELAY_MOVE, SNAP_DELAY_MS, None);
                    }
                } else {
                    // Fallback to immediate move if tray isn't ready (unlikely)
                    move_single_window_if_blocked(hwnd);
                }
            }
        _ => {}
    }
}

/// Populate TOGGLEABLE_MONITORS with all non-primary monitors.
/// Returns the number of toggleable monitors found.
fn populate_toggleable_monitors() -> usize {
    let all = get_all_monitors();
    let mut toggleable = TOGGLEABLE_MONITORS.lock().unwrap();
    toggleable.clear();

    for (_hmon, device_name, rect) in &all {
        // Check if this is the primary monitor
        unsafe {
            let mut info: MONITORINFOEXW = std::mem::zeroed();
            info.monitorInfo.cbSize = std::mem::size_of::<MONITORINFOEXW>() as u32;
            if GetMonitorInfoW(*_hmon, &mut info.monitorInfo as *mut MONITORINFO).as_bool() {
                // MONITORINFOF_PRIMARY = 1
                if info.monitorInfo.dwFlags & 1 != 0 {
                    continue; // Skip primary
                }
            }
        }

        toggleable.push(ToggleableMonitor {
            device_name: device_name.clone(),
            rect: *rect,
            is_disabled: false,
        });
    }

    toggleable.len()
}

#[cfg(debug_assertions)]
/// Toggle disable/enable for a non-primary monitor by its hotkey index.
fn toggle_monitor_by_index(idx: usize) {
    // Read the monitor info and current state
    let (device_name, rect, was_disabled) = {
        let monitors = TOGGLEABLE_MONITORS.lock().unwrap();
        match monitors.get(idx) {
            Some(m) => (m.device_name.clone(), m.rect, m.is_disabled),
            None => return,
        }
    };

    if was_disabled {
        // Re-enable: remove cursor block + restore windows
        {
            let mut rects = BLOCKED_RECTS.lock().unwrap();
            rects.retain(|r| !rects_equal(r, &rect));
        }
        restore_windows_to_monitor(&device_name);
        {
            let mut monitors = TOGGLEABLE_MONITORS.lock().unwrap();
            if let Some(m) = monitors.get_mut(idx) {
                m.is_disabled = false;
            }
        }
        println!("Hotkey: re-enabled {} (cursor unblocked)", device_name);
    } else {
        // Disable: move windows off + block cursor
        move_windows_off_monitor(&rect, &device_name);
        {
            let mut rects = BLOCKED_RECTS.lock().unwrap();
            if !rects.iter().any(|r| rects_equal(r, &rect)) {
                rects.push(rect);
            }
        }
        {
            let mut monitors = TOGGLEABLE_MONITORS.lock().unwrap();
            if let Some(m) = monitors.get_mut(idx) {
                m.is_disabled = true;
            }
        }
        println!(
            "Hotkey: disabled {} (windows moved, cursor blocked)",
            device_name
        );
    }
}

/// Spawn a dedicated thread with a Windows message pump for the mouse hook
/// and global hotkeys (Ctrl+Alt+1..N for each non-primary monitor).
fn spawn_hook_thread(num_toggleable: usize) -> thread::JoinHandle<()> {
    thread::spawn(move || unsafe {
        let num_toggleable = num_toggleable; // suppress unused warning if debug_assertions is off
        let _ = num_toggleable;

        // Initialize tray management
        let _tray = TrayManager::new();

        // Install mouse hook
        let hook = SetWindowsHookExW(WH_MOUSE_LL, Some(mouse_hook_proc), None, 0);
        match hook {
            Ok(_h) => println!("Mouse hook installed"),
            Err(e) => {
                println!("Failed to install mouse hook: {}", e);
                return;
            }
        }

        #[cfg(debug_assertions)]
        {
            // Register hotkeys: Ctrl+Alt+1 .. Ctrl+Alt+N
            let modifiers = MOD_CONTROL | MOD_ALT;
            for i in 0..num_toggleable.min(9) {
                let vk = 0x31 + i as u32; // VK_1 = 0x31, VK_2 = 0x32, ...
                match RegisterHotKey(None, i as i32, modifiers, vk) {
                    Ok(_) => println!("Hotkey Ctrl+Alt+{} registered", i + 1),
                    Err(e) => println!("Failed to register Ctrl+Alt+{}: {}", i + 1, e),
                }
            }
        }

        // Register WinEventHook to catch window lifecycle and state changes.
        // We cover a range from MOVESIZESTART (0x000A) to LOCATIONCHANGE (0x800B)
        // because they are common for top-level window management.
        let _win_hook = SetWinEventHook(
            EVENT_SYSTEM_MOVESIZESTART,
            EVENT_OBJECT_LOCATIONCHANGE,
            None,
            Some(win_event_proc),
            0,
            0,
            WINEVENT_OUTOFCONTEXT,
        );

        // Message pump — handles WH_MOUSE_LL, WM_HOTKEY, WinEvents, and Tray
        let mut msg: MSG = std::mem::zeroed();
        while GetMessageW(&mut msg, None, 0, 0).as_bool() {
            if msg.message == WM_QUIT {
                break;
            }
            #[cfg(debug_assertions)]
            if msg.message == WM_HOTKEY {
                let hotkey_id = msg.wParam.0;
                toggle_monitor_by_index(hotkey_id);
            }
            let _ = TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    })
}

// ─── 5. Main ───────────────────────────────────────────────────────

fn main() {
    // Single instance check
    let mutex_name: Vec<u16> = "Global\\DDC_Check_SingleInstanceMutex\0"
        .encode_utf16()
        .collect();
    let _h_mutex = unsafe {
        let h = CreateMutexW(None, BOOL(0), PCWSTR(mutex_name.as_ptr())).unwrap();
        if GetLastError() == ERROR_ALREADY_EXISTS {
            return;
        }
        h
    };

    println!("Monitor manager running...\n");

    // Discover non-primary monitors and set up hotkeys
    let num_toggleable = populate_toggleable_monitors();
    let _ = num_toggleable; 
    #[cfg(debug_assertions)]
    {
        let monitors = TOGGLEABLE_MONITORS.lock().unwrap();
        if !monitors.is_empty() {
            println!("Toggleable monitors:");
            for (i, m) in monitors.iter().enumerate() {
                println!(
                    "  Ctrl+Alt+{} → {} ({}x{} @ {},{})",
                    i + 1,
                    m.device_name,
                    m.rect.right - m.rect.left,
                    m.rect.bottom - m.rect.top,
                    m.rect.left,
                    m.rect.top,
                );
            }
            println!();
        }
    }

    // Start the mouse hook + hotkey thread (lives for the entire program)
    let _hook_thread = spawn_hook_thread(num_toggleable);

    // Give the hook thread time to install
    thread::sleep(Duration::from_millis(200));

    // State
    let mut debounce: HashMap<String, MonitorDebounce> = HashMap::new();
    let mut disabled: HashSet<String> = HashSet::new();

    while RUNNING.load(Ordering::Relaxed) {
        let adapters = enumerate_adapter_monitors();

        for mut display in Display::enumerate() {
            let info = &display.info;

            let edid = match &info.edid_data {
                Some(e) => e,
                None => continue,
            };

            let id = sha256_hex(edid);

            let name = info
                .model_name
                .clone()
                .unwrap_or_else(|| info.id.clone());

            // Map to Windows device name
            let device_name = match match_display_to_device(info, &adapters) {
                Some(d) => d,
                None => {
                    println!("No device mapping for \"{}\" ({})", name, &id[..8]);
                    continue;
                }
            };

            // Read DDC/CI power state (VCP 0xD6)
            let state = match display.handle.get_vcp_feature(0xD6) {
                Ok(v) => decode_power(v.value()),
                Err(_) => PowerState::Off,
            };

            // ── Debounce ──
            let should_transition = {
                let db = debounce.entry(id.clone()).or_insert_with(|| {
                    // Force an immediate transition if the monitor starts in an Off state
                    MonitorDebounce {
                        confirmed_state: PowerState::On,
                        pending_state: state.clone(),
                        count: DEBOUNCE_THRESHOLD, 
                    }
                });

                if state == db.pending_state {
                    db.count += 1;
                } else {
                    db.pending_state = state.clone();
                    db.count = 1;
                }

                // Check if we've reached threshold and state actually changed
                if db.count >= DEBOUNCE_THRESHOLD && db.pending_state != db.confirmed_state {
                    db.confirmed_state = state.clone();
                    true
                } else {
                    false
                }
            }; // mutable borrow of `debounce` is dropped here

            if !should_transition {
                continue;
            }

            // ── Confirmed state transition ──
            println!("{} ({}) → {:?}", name, device_name, state);

            match state {
                PowerState::Off => {
                    // Count how many monitors are still ON
                    let active_count = debounce
                        .values()
                        .filter(|d| d.confirmed_state == PowerState::On)
                        .count();

                    if active_count == 0 {
                        println!("  Skipped — last active monitor");
                        // Revert the confirmed state so we retry next cycle
                        if let Some(db) = debounce.get_mut(&id) {
                            db.confirmed_state = PowerState::On;
                        }
                        continue;
                    }

                    if let Some(rect) = get_monitor_rect(&device_name) {
                        move_windows_off_monitor(&rect, &device_name);
                        let mut rects = BLOCKED_RECTS.lock().unwrap();
                        if !rects.iter().any(|r| rects_equal(r, &rect)) {
                            rects.push(rect);
                        }
                        disabled.insert(id.clone());
                        println!(
                            "  Disabled: windows moved, cursor blocked ({}x{} @ {},{})",
                            rect.right - rect.left,
                            rect.bottom - rect.top,
                            rect.left,
                            rect.top,
                        );
                    } else {
                        println!("  Could not find monitor rect for {}", device_name);
                    }
                }
                PowerState::On => {
                    // Don't override a manual hotkey disable
                    let manually_disabled = TOGGLEABLE_MONITORS
                        .lock()
                        .unwrap()
                        .iter()
                        .any(|m| m.device_name == device_name && m.is_disabled);

                    if manually_disabled {
                        println!("  Skipped re-enable — manually disabled via hotkey");
                        // Keep disabled state so DDC doesn't keep retrying
                        if let Some(db) = debounce.get_mut(&id) {
                            db.confirmed_state = PowerState::Off;
                        }
                        continue;
                    }

                    if disabled.remove(&id) {
                        if let Some(rect) = get_monitor_rect(&device_name) {
                            let mut rects = BLOCKED_RECTS.lock().unwrap();
                            rects.retain(|r| !rects_equal(r, &rect));
                        }
                        restore_windows_to_monitor(&device_name);
                        println!("  Re-enabled: cursor unblocked, windows restored");
                    }
                }
            }
        }

        thread::sleep(Duration::from_secs(2));
    }
}
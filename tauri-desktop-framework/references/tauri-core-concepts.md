# Tauri Core Concepts Reference

This document covers essential concepts for building Tauri v2.x applications, including window management, application lifecycle, system integration, and architecture patterns.

## Table of Contents

1. [Application Architecture](#application-architecture)
2. [Window Management](#window-management)
3. [Application Lifecycle](#application-lifecycle)
4. [System Integration](#system-integration)
5. [Process Communication](#process-communication)
6. [State Management](#state-management)

---

## Application Architecture

### Frontend + Backend Split

Tauri applications consist of two distinct parts:

**Frontend (Web Technologies):**
- HTML/CSS/JavaScript (React, Vue, Svelte, etc.)
- Runs in a WebView (system browser)
- Handles UI rendering and user interactions
- Communicates with backend via IPC

**Backend (Rust):**
- Compiled Rust code
- Handles system operations, file I/O, native APIs
- Exposes commands to frontend
- Manages application state and lifecycle

### Memory Architecture

```
┌─────────────────────────────────────┐
│  WebView Process (~20-30MB)         │
│  ┌───────────────────────────────┐  │
│  │  HTML/CSS/JavaScript          │  │
│  │  React/Vue/Svelte App         │  │
│  └───────────────────────────────┘  │
│              ↕ IPC                  │
│  ┌───────────────────────────────┐  │
│  │  Rust Backend (~5-10MB)       │  │
│  │  Tauri Commands               │  │
│  │  System APIs                  │  │
│  └───────────────────────────────┘  │
└─────────────────────────────────────┘
Total: ~30-40MB (vs Electron ~200-300MB)
```

---

## Window Management

### Creating Windows

**Programmatically (Rust):**
```rust
use tauri::{Manager, WindowBuilder, WindowUrl};

#[tauri::command]
fn create_window(app: tauri::AppHandle, label: String, url: String) -> Result<(), String> {
    WindowBuilder::new(&app, label, WindowUrl::App(url.into()))
        .title("New Window")
        .inner_size(800.0, 600.0)
        .min_inner_size(400.0, 300.0)
        .resizable(true)
        .decorations(true)
        .transparent(false)
        .always_on_top(false)
        .build()
        .map_err(|e| e.to_string())?;

    Ok(())
}
```

**Declaratively (tauri.conf.json):**
```json
{
  "app": {
    "windows": [
      {
        "label": "main",
        "title": "My App",
        "width": 1200,
        "height": 800,
        "minWidth": 800,
        "minHeight": 600,
        "center": true,
        "resizable": true,
        "fullscreen": false,
        "decorations": true,
        "alwaysOnTop": false,
        "theme": "dark"
      }
    ]
  }
}
```

### Window Control (Frontend)

```typescript
import { Window } from '@tauri-apps/api/window';

const mainWindow = Window.getCurrent();
const specificWindow = Window.getByLabel('settings');

// Window state
await mainWindow.minimize();
await mainWindow.maximize();
await mainWindow.unmaximize();
await mainWindow.show();
await mainWindow.hide();
await mainWindow.close();

// Window properties
await mainWindow.setTitle('New Title');
await mainWindow.setSize(new LogicalSize(1024, 768));
await mainWindow.setPosition(new LogicalPosition(100, 100));
await mainWindow.setResizable(false);
await mainWindow.setAlwaysOnTop(true);

// Window queries
const isMaximized = await mainWindow.isMaximized();
const isVisible = await mainWindow.isVisible();
const size = await mainWindow.innerSize();
const position = await mainWindow.innerPosition();
```

### Multi-Window Patterns

**Settings Window Pattern:**
```rust
// src-tauri/src/windows.rs
use tauri::{Manager, Runtime, Window};

pub fn open_settings<R: Runtime>(app: &tauri::AppHandle<R>) -> Result<Window<R>, tauri::Error> {
    // Check if window already exists
    if let Some(window) = app.get_window("settings") {
        window.set_focus()?;
        return Ok(window);
    }

    // Create new settings window
    tauri::WindowBuilder::new(
        app,
        "settings",
        tauri::WindowUrl::App("settings.html".into())
    )
    .title("Settings")
    .inner_size(600.0, 500.0)
    .resizable(false)
    .center()
    .build()
}
```

**Modal Dialog Pattern:**
```rust
pub fn open_modal<R: Runtime>(
    parent: &Window<R>,
    label: &str,
    url: &str
) -> Result<Window<R>, tauri::Error> {
    tauri::WindowBuilder::new(
        &parent.app_handle(),
        label,
        tauri::WindowUrl::App(url.into())
    )
    .title("Modal")
    .inner_size(400.0, 300.0)
    .resizable(false)
    .center()
    .always_on_top(true)
    .decorations(false)
    .transparent(true)
    .build()
}
```

---

## Application Lifecycle

### Startup Sequence

1. **Rust Entry Point** (`main.rs`)
2. **Builder Configuration** (plugins, commands, state)
3. **Window Creation** (from config or programmatic)
4. **Setup Hook** (one-time initialization)
5. **Ready Event** (app fully initialized)

**Setup Hook Example:**
```rust
fn main() {
    tauri::Builder::default()
        .setup(|app| {
            // One-time initialization
            println!("App is starting up!");

            // Initialize database
            let app_dir = app.path_resolver()
                .app_data_dir()
                .expect("Failed to get app data directory");
            std::fs::create_dir_all(&app_dir)?;

            // Set up logging
            setup_logger(&app_dir)?;

            Ok(())
        })
        .invoke_handler(tauri::generate_handler![/* commands */])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### Shutdown Sequence

**Graceful Cleanup:**
```rust
use tauri::{Manager, RunEvent};

fn main() {
    tauri::Builder::default()
        .build(tauri::generate_context!())
        .expect("error while building tauri application")
        .run(|app_handle, event| match event {
            RunEvent::Exit => {
                println!("App is shutting down");
                // Perform cleanup
                cleanup_resources(app_handle);
            }
            _ => {}
        });
}

fn cleanup_resources(app: &tauri::AppHandle) {
    // Save state
    // Close database connections
    // Clear temporary files
    // Cancel background tasks
}
```

**Prevent Close (Confirmation Dialog):**
```rust
use tauri::Manager;

fn main() {
    tauri::Builder::default()
        .on_window_event(|event| {
            if let tauri::WindowEvent::CloseRequested { api, .. } = event.event() {
                // Prevent default close
                api.prevent_close();

                // Show confirmation dialog
                let window = event.window();
                window.emit("confirm-close", ()).unwrap();
            }
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}

// Frontend handles confirmation
// listen('confirm-close', async () => {
//     if (await confirm('Are you sure you want to quit?')) {
//         await appWindow.close();
//     }
// });
```

---

## System Integration

### System Tray

```rust
use tauri::{CustomMenuItem, SystemTray, SystemTrayMenu, SystemTrayEvent};
use tauri::Manager;

fn main() {
    let quit = CustomMenuItem::new("quit".to_string(), "Quit");
    let show = CustomMenuItem::new("show".to_string(), "Show");
    let tray_menu = SystemTrayMenu::new()
        .add_item(show)
        .add_item(quit);

    let system_tray = SystemTray::new().with_menu(tray_menu);

    tauri::Builder::default()
        .system_tray(system_tray)
        .on_system_tray_event(|app, event| match event {
            SystemTrayEvent::MenuItemClick { id, .. } => {
                match id.as_str() {
                    "quit" => {
                        std::process::exit(0);
                    }
                    "show" => {
                        let window = app.get_window("main").unwrap();
                        window.show().unwrap();
                        window.set_focus().unwrap();
                    }
                    _ => {}
                }
            }
            _ => {}
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### Native Menus

```rust
use tauri::{Menu, MenuItem, Submenu, CustomMenuItem};

fn create_menu() -> Menu {
    let file_menu = Submenu::new(
        "File",
        Menu::new()
            .add_item(CustomMenuItem::new("new", "New"))
            .add_item(CustomMenuItem::new("open", "Open"))
            .add_native_item(MenuItem::Separator)
            .add_native_item(MenuItem::Quit)
    );

    let edit_menu = Submenu::new(
        "Edit",
        Menu::new()
            .add_native_item(MenuItem::Undo)
            .add_native_item(MenuItem::Redo)
            .add_native_item(MenuItem::Separator)
            .add_native_item(MenuItem::Cut)
            .add_native_item(MenuItem::Copy)
            .add_native_item(MenuItem::Paste)
    );

    Menu::new()
        .add_submenu(file_menu)
        .add_submenu(edit_menu)
}

fn main() {
    tauri::Builder::default()
        .menu(create_menu())
        .on_menu_event(|event| {
            match event.menu_item_id() {
                "new" => {
                    // Handle new file
                }
                "open" => {
                    // Handle open file
                }
                _ => {}
            }
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### Global Shortcuts

```rust
use tauri::Manager;
use tauri::GlobalShortcutManager;

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            let mut shortcut = app.global_shortcut_manager();

            shortcut.register("CmdOrCtrl+Shift+C", || {
                println!("Shortcut triggered!");
            })?;

            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

---

## Process Communication

### Command Pattern

**Simple Request-Response:**
```rust
#[tauri::command]
fn calculate(a: i32, b: i32) -> i32 {
    a + b
}
```

**Error Handling:**
```rust
#[tauri::command]
fn read_config(path: String) -> Result<String, String> {
    std::fs::read_to_string(&path)
        .map_err(|e| format!("Failed to read file: {}", e))
}
```

**Async Operations:**
```rust
#[tauri::command]
async fn fetch_data(url: String) -> Result<String, String> {
    reqwest::get(&url)
        .await
        .map_err(|e| e.to_string())?
        .text()
        .await
        .map_err(|e| e.to_string())
}
```

### Event Pattern

**For Progress Updates:**
```rust
use tauri::Manager;

#[tauri::command]
async fn process_batch(
    app: tauri::AppHandle,
    items: Vec<String>
) -> Result<(), String> {
    let total = items.len();

    for (i, item) in items.iter().enumerate() {
        // Process item
        process_item(item)?;

        // Emit progress
        app.emit_all("batch-progress", (i + 1, total))
            .map_err(|e| e.to_string())?;
    }

    Ok(())
}
```

**Frontend Listener:**
```typescript
import { listen } from '@tauri-apps/api/event';

const unlisten = await listen<[number, number]>('batch-progress', (event) => {
    const [current, total] = event.payload;
    const percentage = (current / total) * 100;
    updateProgressBar(percentage);
});

// Cleanup
unlisten();
```

---

## State Management

### App State

**Defining State:**
```rust
use std::sync::Mutex;

struct AppState {
    counter: Mutex<i32>,
    config: Mutex<Config>,
}

impl AppState {
    fn new() -> Self {
        Self {
            counter: Mutex::new(0),
            config: Mutex::new(Config::default()),
        }
    }
}
```

**Using State in Commands:**
```rust
#[tauri::command]
fn increment_counter(state: tauri::State<AppState>) -> i32 {
    let mut counter = state.counter.lock().unwrap();
    *counter += 1;
    *counter
}

fn main() {
    tauri::Builder::default()
        .manage(AppState::new())
        .invoke_handler(tauri::generate_handler![increment_counter])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### Window-Specific State

```rust
use tauri::Manager;

#[tauri::command]
fn set_window_data(window: tauri::Window, key: String, value: String) {
    window.emit(&format!("data-{}", key), value).unwrap();
}
```

---

## Best Practices

### 1. Memory Management
- Use `Arc<Mutex<T>>` for shared state
- Clean up event listeners when components unmount
- Avoid storing large data in frontend state (use backend)

### 2. Error Handling
- Always use `Result<T, String>` for fallible commands
- Provide meaningful error messages
- Log errors for debugging

### 3. Security
- Validate all frontend input in backend
- Use allowlist to restrict file system access
- Never expose sensitive operations without authentication

### 4. Performance
- Use async for I/O operations
- Emit events for progress, not polling
- Keep frontend state minimal
- Offload heavy computation to Rust

---

## References

- Official Docs: https://v2.tauri.app/
- API Reference: https://v2.tauri.app/reference/
- GitHub: https://github.com/tauri-apps/tauri
- Community: https://discord.gg/tauri

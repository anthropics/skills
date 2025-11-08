---
name: tauri-desktop-framework
description: Guide development of cross-platform desktop applications using Tauri v2.x. This skill should be used when building desktop applications with minimal memory footprint (critical for AI/ML workloads), implementing Rust backend commands, configuring IPC communication, setting up window management, or preparing applications for distribution via MSI/DMG/AppImage installers.
---

# Tauri Desktop Framework v2.x

## Overview

This skill provides comprehensive guidance for building production-ready desktop applications using Tauri v2.x, the Rust-based framework that provides a minimal memory footprint (30-40MB vs 200-300MB for Electron). Tauri v2.x is particularly critical for AI/ML applications where every MB of memory translates to available resources for model execution.

**Latest Stable Version:** v2.9.2 (Tauri core), v2.9.3 (CLI)
**Official Documentation:** https://v2.tauri.app/

## When to Use This Skill

Use this skill when:
- Building a new cross-platform desktop application with web technologies
- Migrating from Electron to reduce memory footprint for AI workloads
- Implementing Rust backend commands that communicate with frontend
- Configuring window management, system tray, or native menus
- Setting up IPC (Inter-Process Communication) between frontend and backend
- Preparing application distribution with code signing and installers
- Optimizing memory usage for resource-intensive applications

## Core Capabilities

### 1. Project Initialization

To create a new Tauri project, use the official scaffolding tool:

```bash
# Using npm
npm create tauri-app@latest

# Using cargo
cargo install create-tauri-app
cargo create-tauri-app
```

For a production-ready setup with React + TypeScript, use the initialization script:

```bash
scripts/init-tauri-project.sh my-app react-ts
```

This creates a properly configured project with:
- Tauri v2.9.x configuration
- TypeScript strict mode enabled
- Vite build system optimized for production
- Security-first defaults (CSP, allowlist)

### 2. Window Management

Tauri provides fine-grained control over application windows. To create and manage windows:

**Creating Windows (Rust):**
```rust
use tauri::window::WindowBuilder;

#[tauri::command]
fn open_settings_window(app: tauri::AppHandle) -> Result<(), String> {
    WindowBuilder::new(
        &app,
        "settings",
        tauri::WindowUrl::App("settings.html".into())
    )
    .title("Settings")
    .inner_size(800.0, 600.0)
    .resizable(true)
    .build()
    .map_err(|e| e.to_string())?;
    Ok(())
}
```

**Controlling Windows (Frontend):**
```typescript
import { Window } from '@tauri-apps/api/window';

// Get current window
const appWindow = Window.getCurrent();

// Minimize, maximize, close
await appWindow.minimize();
await appWindow.maximize();
await appWindow.close();

// Set title dynamically
await appWindow.setTitle('My App - Editing');
```

See `references/tauri-core-concepts.md` for comprehensive window management patterns.

### 3. Tauri Commands (IPC)

Tauri commands expose Rust functions to the frontend via a secure IPC layer. Functions must be explicitly marked with `#[tauri::command]`:

**Backend (Rust):**
```rust
// src-tauri/src/commands.rs
#[tauri::command]
fn greet(name: String) -> String {
    format!("Hello, {}!", name)
}

#[tauri::command]
async fn process_image(path: String) -> Result<Vec<u8>, String> {
    // Async operations work seamlessly
    tokio::fs::read(&path)
        .await
        .map_err(|e| e.to_string())
}

// Register in main.rs
fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![greet, process_image])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

**Frontend (TypeScript):**
```typescript
import { invoke } from '@tauri-apps/api/tauri';

// Call Rust command
const message = await invoke<string>('greet', { name: 'World' });

// Handle async operations with proper typing
try {
    const imageData = await invoke<number[]>('process_image', {
        path: '/path/to/image.png'
    });
} catch (error) {
    console.error('Failed to process image:', error);
}
```

### 4. Event System

For streaming data or progress updates, use Tauri's event system:

**Emitting Events (Rust):**
```rust
use tauri::Manager;

#[tauri::command]
async fn long_running_task(app: tauri::AppHandle) -> Result<(), String> {
    for i in 0..100 {
        // Emit progress events
        app.emit_all("task-progress", i).map_err(|e| e.to_string())?;
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
    Ok(())
}
```

**Listening to Events (Frontend):**
```typescript
import { listen } from '@tauri-apps/api/event';

const unlisten = await listen<number>('task-progress', (event) => {
    console.log(`Progress: ${event.payload}%`);
    updateProgressBar(event.payload);
});

// Clean up listener when component unmounts
unlisten();
```

### 5. File System Access

Tauri provides secure file system APIs with user consent dialogs:

```typescript
import { open, save } from '@tauri-apps/api/dialog';
import { readTextFile, writeTextFile } from '@tauri-apps/api/fs';

// Open file dialog
const selected = await open({
    multiple: false,
    filters: [{
        name: 'Image',
        extensions: ['png', 'jpg', 'jpeg']
    }]
});

if (selected) {
    // Read file (Rust handles actual I/O)
    const contents = await readTextFile(selected as string);
}

// Save file dialog
const savePath = await save({
    filters: [{
        name: 'JSON',
        extensions: ['json']
    }]
});

if (savePath) {
    await writeTextFile(savePath, JSON.stringify(data));
}
```

### 6. Asset Protocol for Large Files

For bundling large files (models, datasets), use the asset protocol:

**Configuration (tauri.conf.json):**
```json
{
  "tauri": {
    "bundle": {
      "resources": [
        "models/*.gguf",
        "models/*.safetensors",
        "assets/large-dataset.bin"
      ]
    }
  }
}
```

**Accessing Assets (Frontend/Backend):**
```rust
use tauri::Manager;

#[tauri::command]
fn load_model(app: tauri::AppHandle) -> Result<String, String> {
    // Get path to bundled resource
    let resource_path = app.path_resolver()
        .resolve_resource("models/flux-kontext.gguf")
        .ok_or("Failed to resolve resource")?;

    Ok(resource_path.to_string_lossy().to_string())
}
```

See `references/tauri-api-reference.md` for complete API documentation.

### 7. Security Model

Tauri enforces security by default:

**Content Security Policy:**
```json
{
  "tauri": {
    "security": {
      "csp": "default-src 'self'; img-src 'self' asset: https://asset.localhost"
    }
  }
}
```

**Function Allowlist:**
Only explicitly exposed commands are callable from frontend. Never use `allowAll` in production:

```json
{
  "tauri": {
    "allowlist": {
      "fs": {
        "scope": ["$APPDATA/*", "$RESOURCE/*"],
        "readFile": true,
        "writeFile": true
      },
      "dialog": {
        "open": true,
        "save": true
      }
    }
  }
}
```

### 8. Building and Distribution

Tauri supports multiple distribution formats per platform:

**Build Commands:**
```bash
# Development build
npm run tauri dev

# Production build
npm run tauri build

# Build for specific platform (cross-compilation)
npm run tauri build -- --target x86_64-pc-windows-msvc
```

**Generated Installers:**
- **Windows:** `.msi` (Windows Installer), `.exe` (NSIS)
- **macOS:** `.dmg` (Disk Image), `.app` (Application Bundle)
- **Linux:** `.AppImage`, `.deb`, `.rpm`

**Code Signing Configuration:**

For Windows (tauri.conf.json):
```json
{
  "tauri": {
    "bundle": {
      "windows": {
        "certificateThumbprint": "YOUR_CERT_THUMBPRINT",
        "digestAlgorithm": "sha256",
        "timestampUrl": "http://timestamp.digicert.com"
      }
    }
  }
}
```

For macOS, set environment variables:
```bash
export APPLE_CERTIFICATE="Developer ID Application: Your Name (TEAM_ID)"
export APPLE_CERTIFICATE_PASSWORD="cert_password"
export APPLE_ID="your@email.com"
export APPLE_PASSWORD="app-specific-password"
```

See `references/tauri-bundler-config.md` for platform-specific configuration details.

### 9. Auto-Updater

Enable seamless updates with Tauri's built-in updater:

**Configuration:**
```json
{
  "tauri": {
    "updater": {
      "active": true,
      "endpoints": [
        "https://releases.myapp.com/{{target}}/{{current_version}}"
      ],
      "dialog": true,
      "pubkey": "YOUR_PUBLIC_KEY"
    }
  }
}
```

**Frontend Integration:**
```typescript
import { checkUpdate, installUpdate } from '@tauri-apps/api/updater';
import { relaunch } from '@tauri-apps/api/process';

try {
    const { shouldUpdate, manifest } = await checkUpdate();

    if (shouldUpdate) {
        console.log(`Update available: ${manifest?.version}`);
        await installUpdate();
        await relaunch();
    }
} catch (error) {
    console.error('Update check failed:', error);
}
```

### 10. Performance Optimization

**Memory Footprint:**
- Base Tauri app: 30-40MB (vs 200-300MB Electron)
- Use system WebView (no Chromium bundle)
- Critical for AI applications with large model memory requirements

**Build Optimization:**
```json
{
  "tauri": {
    "bundle": {
      "externalBin": ["path/to/python-backend"],
      "resources": ["models/*"]
    }
  }
}
```

**Rust Optimization (Cargo.toml):**
```toml
[profile.release]
opt-level = "z"     # Optimize for size
lto = true          # Enable Link Time Optimization
codegen-units = 1   # Better optimization (slower compile)
strip = true        # Strip symbols
```

## Quick Reference

**Common Commands:**
- `npm create tauri-app@latest` - Create new project
- `npm run tauri dev` - Development mode with hot reload
- `npm run tauri build` - Production build
- `npm run tauri info` - System and dependency information
- `npm run tauri icon` - Generate app icons from source

**Key Configuration Files:**
- `src-tauri/tauri.conf.json` - Main Tauri configuration
- `src-tauri/Cargo.toml` - Rust dependencies
- `src-tauri/src/main.rs` - Application entry point
- `src-tauri/src/commands.rs` - Backend command handlers

**Critical Documentation Links:**
- Main docs: https://v2.tauri.app/
- API reference: https://v2.tauri.app/reference/
- Security guide: https://v2.tauri.app/security/
- Distribution: https://v2.tauri.app/distribute/

## Resources

This skill includes the following bundled resources:

### scripts/
- `init-tauri-project.sh` - Initialize production-ready Tauri project with best practices

### references/
- `tauri-core-concepts.md` - Window management, lifecycle, system integration
- `tauri-api-reference.md` - Complete @tauri-apps/api TypeScript API documentation
- `tauri-bundler-config.md` - Platform-specific MSI/DMG/AppImage configuration

### assets/
- `tauri.conf.json-template` - Production-ready configuration template with security defaults

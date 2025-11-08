# Platform-Specific Cache Locations

## Overview

Different operating systems have established conventions for where applications should store cache and data files. Respecting these conventions improves user experience, supports system maintenance, and complies with OS guidelines.

## Standard Cache Directories

### Windows

**Primary Location:**
```
%APPDATA%\{AppName}\cache\models
```

**Expanded Path Examples:**
```
C:\Users\Username\AppData\Roaming\MyApp\cache\models
```

**Alternative (per-user local data):**
```
%LOCALAPPDATA%\{AppName}\cache\models
C:\Users\Username\AppData\Local\MyApp\cache\models
```

**Alternative (ProgramData for shared models):**
```
%ProgramData%\{AppName}\cache\models
C:\ProgramData\MyApp\cache\models
```

### macOS

**Primary Location:**
```
~/Library/Application Support/{AppName}/cache/models
```

**Expanded Path Examples:**
```
/Users/username/Library/Application Support/MyApp/cache/models
```

**Alternative (macOS Caches directory):**
```
~/Library/Caches/{AppName}/models
/Users/username/Library/Caches/MyApp/models
```

**Note:** Use `~/Library/Application Support/` for persistent cache that survives system cleanup.

### Linux (XDG Base Directory Specification)

**Primary Location (respects XDG standards):**
```
$XDG_CACHE_HOME/{appname}/models
```
(Defaults to `~/.cache/{appname}/models` if `$XDG_CACHE_HOME` not set)

**Alternative (fallback):**
```
~/.config/{appname}/cache/models
```

**Expanded Path Examples:**
```
/home/username/.cache/myapp/models
~/.cache/myapp/models
```

**Note:** Some distros use different structures; respect `$XDG_CACHE_HOME` environment variable.

## Implementation Examples

### Rust with Tauri

Using `tauri::api::path` for cross-platform paths:

```rust
use tauri::api::path::cache_dir;

#[tauri::command]
fn get_model_cache_dir(app_handle: tauri::AppHandle) -> Result<String, String> {
    match cache_dir(&app_handle.config()) {
        Some(path) => {
            let model_cache = path.join("models");
            Ok(model_cache.to_string_lossy().to_string())
        }
        None => Err("Could not determine cache directory".to_string()),
    }
}
```

### TypeScript Implementation

```typescript
import { appDir, cacheDir } from '@tauri-apps/api/path';
import { invoke } from '@tauri-apps/api/tauri';

export async function getModelCacheDir(): Promise<string> {
    try {
        const cacheDirectory = await cacheDir();
        return `${cacheDirectory}models`;
    } catch (error) {
        console.error('Failed to determine cache directory:', error);
        throw error;
    }
}

// Platform-specific implementation (manual)
export async function getModelCacheDirManual(): Promise<string> {
    const platform = await invoke<string>('get_platform');

    switch (platform) {
        case 'win32':
            return `${process.env.APPDATA}\\MyApp\\cache\\models`;
        case 'darwin':
            return `${process.env.HOME}/Library/Application Support/MyApp/cache/models`;
        case 'linux':
            const xdgCache = process.env.XDG_CACHE_HOME || `${process.env.HOME}/.cache`;
            return `${xdgCache}/myapp/models`;
        default:
            throw new Error(`Unsupported platform: ${platform}`);
    }
}
```

### Python Implementation

```python
import os
import platform
from pathlib import Path

def get_model_cache_dir(app_name: str = "myapp") -> Path:
    """Get platform-appropriate cache directory for models."""
    system = platform.system()

    if system == "Windows":
        # Windows: %APPDATA%\{AppName}\cache\models
        appdata = os.getenv("APPDATA")
        if not appdata:
            raise RuntimeError("APPDATA environment variable not set")
        cache_dir = Path(appdata) / app_name / "cache" / "models"

    elif system == "Darwin":
        # macOS: ~/Library/Application Support/{AppName}/cache/models
        home = Path.home()
        cache_dir = home / "Library" / "Application Support" / app_name / "cache" / "models"

    elif system == "Linux":
        # Linux: $XDG_CACHE_HOME/{appname}/models or ~/.cache/{appname}/models
        xdg_cache = os.getenv("XDG_CACHE_HOME")
        if xdg_cache:
            cache_dir = Path(xdg_cache) / app_name / "models"
        else:
            home = Path.home()
            cache_dir = home / ".cache" / app_name / "models"

    else:
        raise RuntimeError(f"Unsupported platform: {system}")

    return cache_dir

def ensure_cache_dir_exists(app_name: str = "myapp") -> Path:
    """Ensure cache directory exists and is writable."""
    cache_dir = get_model_cache_dir(app_name)
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Verify writability
    if not os.access(cache_dir, os.W_OK):
        raise PermissionError(f"Cache directory not writable: {cache_dir}")

    return cache_dir

# Usage
cache_path = ensure_cache_dir_exists("myapp")
print(f"Model cache directory: {cache_path}")
```

## Tauri Helper Functions

### Complete Configuration

```rust
use tauri::api::path::{cache_dir, data_dir, config_dir};
use std::path::PathBuf;

pub struct AppPaths {
    pub cache_dir: PathBuf,
    pub model_cache_dir: PathBuf,
    pub config_dir: PathBuf,
    pub data_dir: PathBuf,
}

pub fn get_app_paths(app_handle: &tauri::AppHandle) -> Result<AppPaths, String> {
    let config = &app_handle.config();

    let cache_base = cache_dir(config)
        .ok_or("Could not determine cache directory")?;
    let model_cache_dir = cache_base.join("models");

    let config_base = config_dir(config)
        .ok_or("Could not determine config directory")?;

    let data_base = data_dir(config)
        .ok_or("Could not determine data directory")?;

    Ok(AppPaths {
        cache_dir: cache_base,
        model_cache_dir,
        config_dir: config_base,
        data_dir: data_base,
    })
}

#[tauri::command]
fn get_cache_paths(app_handle: tauri::AppHandle) -> Result<serde_json::Value, String> {
    let paths = get_app_paths(&app_handle)?;

    Ok(serde_json::json!({
        "cache_dir": paths.cache_dir.to_string_lossy(),
        "model_cache_dir": paths.model_cache_dir.to_string_lossy(),
        "config_dir": paths.config_dir.to_string_lossy(),
        "data_dir": paths.data_dir.to_string_lossy(),
    }))
}
```

## Directory Creation and Management

### Safe Directory Creation

```rust
use std::fs;
use std::io;

pub fn ensure_model_cache_exists(cache_dir: &Path) -> Result<(), io::Error> {
    // Create directory with all parent directories
    fs::create_dir_all(cache_dir)?;

    // Set permissions on Linux/macOS (700 = rwx------)
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let permissions = fs::Permissions::from_mode(0o700);
        fs::set_permissions(cache_dir, permissions)?;
    }

    Ok(())
}

pub fn get_available_space(path: &Path) -> Result<u64, io::Error> {
    #[cfg(target_os = "windows")]
    {
        use std::os::windows::fs::MetadataExt;
        let metadata = fs::metadata(path)?;
        Ok(metadata.file_size())
    }

    #[cfg(target_os = "macos")]
    {
        use std::os::macos::fs::MetadataExt;
        let metadata = fs::metadata(path)?;
        Ok(metadata.st_blocks() * 512)
    }

    #[cfg(target_os = "linux")]
    {
        use nix::sys::statvfs::statvfs;
        let stats = statvfs(path)?;
        Ok(stats.blocks_available() * stats.block_size())
    }

    #[cfg(not(any(target_os = "windows", target_os = "macos", target_os = "linux")))]
    {
        Err(io::Error::new(io::ErrorKind::Unsupported, "Unsupported platform"))
    }
}
```

### Cleanup and Maintenance

```rust
use std::time::SystemTime;

pub fn cleanup_old_cache(
    cache_dir: &Path,
    max_age_days: u64,
) -> Result<u64, Box<dyn std::error::Error>> {
    let mut removed_bytes = 0;
    let cutoff = SystemTime::now() - std::time::Duration::from_secs(max_age_days * 86400);

    for entry in fs::read_dir(cache_dir)? {
        let entry = entry?;
        let path = entry.path();
        let metadata = entry.metadata()?;

        if let Ok(modified) = metadata.modified() {
            if modified < cutoff {
                let size = metadata.len();
                fs::remove_file(&path)?;
                removed_bytes += size;
            }
        }
    }

    Ok(removed_bytes)
}

pub fn get_cache_size(cache_dir: &Path) -> Result<u64, Box<dyn std::error::Error>> {
    let mut total_size = 0;

    for entry in fs::read_dir(cache_dir)? {
        let entry = entry?;
        let metadata = entry.metadata()?;
        total_size += metadata.len();
    }

    Ok(total_size)
}
```

## Environment Variables

### Configuration via Environment Variables

Allow users to override cache locations:

```rust
pub fn get_model_cache_dir_with_override(app_name: &str) -> Result<PathBuf, String> {
    // Check for environment variable override
    if let Ok(custom_path) = std::env::var("MODEL_CACHE_DIR") {
        return Ok(PathBuf::from(custom_path));
    }

    // Fall back to platform-specific defaults
    get_default_model_cache_dir(app_name)
}

fn get_default_model_cache_dir(app_name: &str) -> Result<PathBuf, String> {
    let system = std::env::consts::OS;

    match system {
        "windows" => {
            let appdata = std::env::var("APPDATA")
                .map_err(|_| "APPDATA not set".to_string())?;
            Ok(PathBuf::from(format!("{}\\{}\\cache\\models", appdata, app_name)))
        }
        "macos" => {
            let home = std::env::var("HOME")
                .map_err(|_| "HOME not set".to_string())?;
            Ok(PathBuf::from(format!(
                "{}/Library/Application Support/{}/cache/models",
                home, app_name
            )))
        }
        "linux" => {
            let xdg_cache = std::env::var("XDG_CACHE_HOME").ok();
            let home = std::env::var("HOME")
                .map_err(|_| "HOME not set".to_string())?;

            let path = if let Some(xdg) = xdg_cache {
                format!("{}/{}/models", xdg, app_name)
            } else {
                format!("{}/.cache/{}/models", home, app_name)
            };

            Ok(PathBuf::from(path))
        }
        _ => Err(format!("Unsupported OS: {}", system)),
    }
}
```

## Symbolic Links and Network Drives

### Handle Network Storage

```rust
pub fn is_network_path(path: &Path) -> bool {
    #[cfg(target_os = "windows")]
    {
        path.to_string_lossy().starts_with("\\\\")
    }

    #[cfg(not(target_os = "windows"))]
    {
        false // Network paths less common on Unix systems
    }
}

pub fn is_symlink(path: &Path) -> Result<bool, io::Error> {
    let metadata = fs::symlink_metadata(path)?;
    Ok(metadata.is_symlink())
}

pub fn resolve_cache_path(path: &Path) -> Result<PathBuf, io::Error> {
    // Resolve symlinks and get canonical path
    fs::canonicalize(path)
}
```

## Testing Cache Paths

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_dir_creation() {
        let temp_dir = tempfile::tempdir().unwrap();
        let cache_dir = temp_dir.path().join("models");

        assert!(ensure_model_cache_exists(&cache_dir).is_ok());
        assert!(cache_dir.exists());
    }

    #[test]
    fn test_platform_paths() {
        let system = std::env::consts::OS;

        match system {
            "windows" => assert!(std::env::var("APPDATA").is_ok()),
            "macos" | "linux" => assert!(std::env::var("HOME").is_ok()),
            _ => {}
        }
    }
}
```

## Migration Between Versions

### Handling Cache Migration

```rust
pub fn migrate_cache_location(
    old_cache_dir: &Path,
    new_cache_dir: &Path,
) -> Result<u64, Box<dyn std::error::Error>> {
    fs::create_dir_all(new_cache_dir)?;
    let mut migrated_bytes = 0;

    for entry in fs::read_dir(old_cache_dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_name = entry.file_name();

        let dest = new_cache_dir.join(&file_name);
        fs::rename(&path, &dest)?;
        migrated_bytes += entry.metadata()?.len();
    }

    // Remove old directory if empty
    let _ = fs::remove_dir(old_cache_dir);

    Ok(migrated_bytes)
}
```

## Best Practices

1. **Follow OS Conventions** - Respect standard cache directories
2. **Handle Missing Directories** - Create cache dirs if they don't exist
3. **Check Permissions** - Verify write access before downloading
4. **Monitor Disk Space** - Warn users before storing large models
5. **Support Overrides** - Allow environment variables to override defaults
6. **Clean Up** - Implement cache cleanup for old/unused models
7. **Document Paths** - Show users where models are stored
8. **Test Across Platforms** - Verify paths work on all target OS versions

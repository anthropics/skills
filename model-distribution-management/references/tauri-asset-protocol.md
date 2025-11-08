# Tauri Asset Protocol for Bundled Models

## Overview

The Tauri asset protocol (`asset://`) enables bundling large model files directly into application installers for immediate offline access. This eliminates the need for separate downloads while keeping the installation straightforward.

## Configuration in tauri.conf.json

Configure resource embedding in `src-tauri/tauri.conf.json`:

```json
{
  "build": {
    "resources": [
      "models/",
      "assets/"
    ]
  }
}
```

This configuration includes the `models/` directory in the bundled resources, making files accessible via `asset://` URLs.

## Asset Protocol URL Format

Access bundled resources using the `asset://` protocol:

```
asset://models/model-name.onnx
asset://models/llama2-7b.bin
asset://models/stable-diffusion.safetensors
```

## Backend Implementation (Rust)

### Resolving Asset Paths

```rust
use tauri::api::path::resource_dir;
use std::path::PathBuf;

fn get_asset_path(app_handle: &tauri::AppHandle, relative_path: &str) -> Result<PathBuf, String> {
    resource_dir(&app_handle.config(), app_handle.package_info())
        .map(|base| base.join(relative_path))
        .map_err(|_| "Failed to resolve resource directory".to_string())
}

// Usage in Tauri command
#[tauri::command]
fn get_bundled_model(
    app_handle: tauri::AppHandle,
    model_name: String,
) -> Result<String, String> {
    let model_path = get_asset_path(&app_handle, &format!("models/{}", model_name))?;
    Ok(model_path.to_string_lossy().to_string())
}
```

### Serving Assets with Custom Protocol

For direct file serving in UI:

```rust
#[cfg_attr(mobile, tauri::mobile::app_entry)]
pub fn run() {
    tauri::Builder::default()
        .register_uri_scheme_protocol("asset", |_app, request| {
            // Handle asset:// URL scheme
            let path = request.uri().path();
            // Resolve and serve file content
            tauri::http::ResponseBuilder::new()
                .status(200)
                .body(vec![])
                .build()
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

## Frontend Integration (TypeScript)

### Loading Bundled Models in UI

```typescript
import { invoke } from '@tauri-apps/api/tauri';

async function loadBundledModel(modelName: string): Promise<string> {
    try {
        const modelPath = await invoke<string>('get_bundled_model', {
            modelName: modelName
        });
        console.log(`Model loaded from: ${modelPath}`);
        return modelPath;
    } catch (error) {
        console.error(`Failed to load model: ${error}`);
        throw error;
    }
}

// Usage
const modelPath = await loadBundledModel('llama2-7b.bin');
const model = await loadModel(modelPath);
```

### Checking Asset Availability

```typescript
async function checkAssetExists(assetPath: string): Promise<boolean> {
    try {
        const result = await invoke<boolean>('check_asset', {
            path: assetPath
        });
        return result;
    } catch {
        return false;
    }
}

// Usage
const hasModel = await checkAssetExists('models/my-model.onnx');
if (hasModel) {
    // Use bundled model
} else {
    // Download model on-demand
}
```

## Resource Organization

### Directory Structure

```
src-tauri/
├── tauri.conf.json
├── src/
│   └── main.rs
└── models/
    ├── llama2-7b.bin
    ├── stable-diffusion.safetensors
    └── metadata.json
```

### Size Considerations

- **Bundled assets** increase installer size significantly
- **Typical model sizes:** 7B parameter models = 14-28GB
- **Strategy:** Bundle only critical models; download specialized models on-demand
- **Maximum recommended:** Include models < 500MB per model or < 2GB total

### Selective Bundling

For large models, bundle only essential files:

```json
{
  "build": {
    "resources": [
      "models/critical-model.bin",
      "models/metadata.json"
    ]
  }
}
```

## Loading Models from Assets

### ONNX Model Loading

```rust
#[tauri::command]
async fn load_onnx_model(
    app_handle: tauri::AppHandle,
    model_name: String,
) -> Result<String, String> {
    let model_path = get_asset_path(&app_handle, &format!("models/{}", model_name))?;

    // Verify file exists
    if !model_path.exists() {
        return Err("Model file not found in assets".to_string());
    }

    // Load ONNX model
    let session = ort::Session::builder()?
        .commit_from_file(&model_path)
        .map_err(|e| e.to_string())?;

    Ok(format!("Model loaded successfully from {:?}", model_path))
}
```

### PyTorch Model Loading

```python
import torch
from pathlib import Path

def load_bundled_torch_model(model_name: str) -> torch.nn.Module:
    """Load a PyTorch model from bundled assets."""
    asset_dir = Path(__file__).parent.parent / "models"
    model_path = asset_dir / model_name

    if not model_path.exists():
        raise FileNotFoundError(f"Model not found: {model_path}")

    model = torch.load(model_path)
    model.eval()
    return model
```

## Platform-Specific Behavior

### Windows
- Assets bundled into executable or `.exe` directory
- Access via `asset://` protocol works seamlessly
- Path separator: `\`

### macOS
- Assets bundled into `.app` bundle contents
- Resources in `Contents/Resources/`
- Path separator: `/`

### Linux
- Assets stored in installation directory
- Resources relative to executable
- Path separator: `/`

## Best Practices

1. **Minimize Bundle Size**
   - Bundle only essential models
   - Use quantized/compressed model versions
   - Store large models externally with on-demand download

2. **Version Management**
   - Include version metadata in bundled assets
   - Track asset versions in manifest
   - Plan for future updates (on-demand download fallback)

3. **Fallback Strategies**
   - If asset missing, download from network
   - Implement asset integrity checks
   - Provide user feedback during loading

4. **Performance**
   - Bundle critical startup models
   - Load large models asynchronously
   - Cache loaded models in memory

5. **Security**
   - Verify asset integrity (checksums)
   - Sign bundled assets
   - Encrypt sensitive models before bundling

## Troubleshooting

### Asset Not Found
- Verify path in `tauri.conf.json` matches actual directory structure
- Check resource path matches exactly (case-sensitive on Linux/macOS)
- Ensure trailing slashes in directory paths: `"models/"`

### Permission Denied
- On Linux/macOS, ensure resource files are readable
- Verify asset directory ownership and permissions

### Large File Issues
- Keep bundled models < 2GB total
- Consider platform-specific builds with different models
- Use lazy loading for optional models

## References

- [Tauri API - Resource Directory](https://tauri.app/v1/api/rust/tauri/api/path/fn.resource_dir.html)
- [Tauri Configuration - Build Resources](https://tauri.app/v1/api/config/#buildconfig.resources)
- [Tauri Protocols](https://tauri.app/v1/guides/features/protocol/)

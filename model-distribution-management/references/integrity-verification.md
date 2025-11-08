# Integrity Verification & Checksum Validation

## Overview

SHA256 checksums provide cryptographically secure verification that downloaded models haven't been corrupted, tampered with, or incompletely downloaded. This is essential for 7-20GB files where corruption is statistically likely.

## SHA256 Hashing Fundamentals

### What is SHA256?

SHA-256 (Secure Hash Algorithm 256-bit) produces a unique 64-character hex string for any file:
- **Deterministic:** Same file always produces same hash
- **Avalanche Effect:** Single bit change produces completely different hash
- **Non-Reversible:** Cannot recreate file from hash
- **Industry Standard:** Widely trusted and supported

### Hash Collision Probability

For practical purposes, SHA256 is collision-proof:
- Expected collisions: 1 in 2^256 attempts
- Total atoms in universe: ~10^80
- Probability of accidental collision: Effectively zero

## Generate Checksums

### Pre-Download Checksum Generation

Generate checksums when preparing models for distribution:

```python
import hashlib
import json
from pathlib import Path
from typing import Dict

def calculate_sha256(file_path: Path, chunk_size: int = 8192) -> str:
    """Calculate SHA256 hash of a file efficiently (streaming)."""
    sha256_hash = hashlib.sha256()

    with open(file_path, 'rb') as f:
        for chunk in iter(lambda: f.read(chunk_size), b''):
            sha256_hash.update(chunk)

    return sha256_hash.hexdigest()

def generate_model_checksums(models_dir: Path) -> Dict[str, Dict]:
    """Generate checksums for all models in a directory."""
    model_checksums = {}

    for model_file in models_dir.glob('*.bin'):
        file_size = model_file.stat().st_size
        checksum = calculate_sha256(model_file)

        model_checksums[model_file.name] = {
            'sha256': checksum,
            'size': file_size,
            'size_gb': round(file_size / (1024**3), 2),
        }

        print(f"{model_file.name}: {checksum[:16]}... ({file_size / (1024**3):.2f} GB)")

    return model_checksums

def save_checksum_manifest(checksums: Dict, output_file: Path):
    """Save checksums to JSON manifest for distribution."""
    with open(output_file, 'w') as f:
        json.dump(checksums, f, indent=2)

# Usage
model_dir = Path("/path/to/models")
checksums = generate_model_checksums(model_dir)
save_checksum_manifest(checksums, Path("model-checksums.json"))
```

### Batch Generation Script

```bash
#!/bin/bash
# generate_checksums.sh

MODELS_DIR="$1"
OUTPUT_FILE="${2:-checksums.json}"

echo "Generating SHA256 checksums for models in $MODELS_DIR"
echo "{" > "$OUTPUT_FILE"

first=true
for model in "$MODELS_DIR"/*.{bin,onnx,safetensors}; do
    if [ -f "$model" ]; then
        if [ "$first" = false ]; then
            echo "," >> "$OUTPUT_FILE"
        fi
        first=false

        filename=$(basename "$model")
        checksum=$(sha256sum "$model" | awk '{print $1}')
        size=$(stat -f%z "$model" 2>/dev/null || stat -c%s "$model")

        echo -n "  \"$filename\": {\"sha256\": \"$checksum\", \"size\": $size}" >> "$OUTPUT_FILE"
    fi
done

echo "" >> "$OUTPUT_FILE"
echo "}" >> "$OUTPUT_FILE"

echo "Checksums saved to $OUTPUT_FILE"
```

## Verify Checksums

### Rust Implementation

```rust
use std::fs::File;
use std::io::{Read, Result as IoResult};
use std::path::Path;
use sha2::{Sha256, Digest};

pub fn verify_file_checksum(
    file_path: &Path,
    expected_checksum: &str,
) -> Result<bool, Box<dyn std::error::Error>> {
    let calculated = calculate_file_checksum(file_path)?;
    Ok(calculated.eq_ignore_ascii_case(expected_checksum))
}

pub fn calculate_file_checksum(file_path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    let mut file = File::open(file_path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0; 8192];

    loop {
        let bytes_read = file.read(&mut buffer)?;
        if bytes_read == 0 {
            break;
        }
        hasher.update(&buffer[..bytes_read]);
    }

    Ok(format!("{:x}", hasher.finalize()))
}

#[tauri::command]
async fn verify_model_integrity(
    model_path: String,
    expected_checksum: String,
) -> Result<bool, String> {
    let path = Path::new(&model_path);
    verify_file_checksum(path, &expected_checksum)
        .map_err(|e| e.to_string())
}
```

### Python Implementation

```python
import hashlib
from pathlib import Path

def verify_model_checksum(
    file_path: Path,
    expected_checksum: str,
    chunk_size: int = 8192
) -> bool:
    """Verify file against expected SHA256 checksum."""
    calculated = calculate_sha256(file_path, chunk_size)
    return calculated.lower() == expected_checksum.lower()

def calculate_sha256(
    file_path: Path,
    chunk_size: int = 8192
) -> str:
    """Calculate SHA256 hash of file."""
    sha256_hash = hashlib.sha256()

    try:
        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(chunk_size), b''):
                sha256_hash.update(chunk)
    except IOError as e:
        raise ValueError(f"Cannot read file: {file_path}") from e

    return sha256_hash.hexdigest()

def verify_with_progress(
    file_path: Path,
    expected_checksum: str,
    on_progress=None
) -> bool:
    """Verify checksum with progress callback."""
    sha256_hash = hashlib.sha256()
    file_size = file_path.stat().st_size
    bytes_processed = 0

    with open(file_path, 'rb') as f:
        while True:
            chunk = f.read(8192)
            if not chunk:
                break
            sha256_hash.update(chunk)
            bytes_processed += len(chunk)

            if on_progress:
                percentage = (bytes_processed / file_size) * 100
                on_progress(percentage, bytes_processed, file_size)

    calculated = sha256_hash.hexdigest()
    return calculated.lower() == expected_checksum.lower()

# Usage with progress
def progress_callback(percent, current, total):
    print(f"Verifying: {percent:.1f}% ({current}/{total} bytes)")

is_valid = verify_with_progress(
    Path("large_model.bin"),
    "abc123...",
    progress_callback
)
```

### TypeScript Implementation

```typescript
import { invoke } from '@tauri-apps/api/tauri';
import * as fs from 'fs';
import * as crypto from 'crypto';

export async function verifyModelIntegrity(
    modelPath: string,
    expectedChecksum: string
): Promise<boolean> {
    return invoke<boolean>('verify_model_integrity', {
        modelPath,
        expectedChecksum,
    });
}

// Browser-side verification (if downloaded to browser)
export async function verifyChecksumInBrowser(
    file: File,
    expectedChecksum: string
): Promise<boolean> {
    const arrayBuffer = await file.arrayBuffer();
    const hashBuffer = await crypto.subtle.digest('SHA-256', arrayBuffer);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    const hashHex = hashArray
        .map(b => b.toString(16).padStart(2, '0'))
        .join('');

    return hashHex.toLowerCase() === expectedChecksum.toLowerCase();
}

// Progress-based verification
export async function verifyWithProgress(
    file: File,
    expectedChecksum: string,
    onProgress?: (percentage: number) => void
): Promise<boolean> {
    const chunkSize = 1024 * 1024; // 1MB chunks
    let offset = 0;
    const hashObject = { data: new Uint8Array() };

    while (offset < file.size) {
        const chunk = file.slice(offset, offset + chunkSize);
        const arrayBuffer = await chunk.arrayBuffer();

        // Accumulate chunks for final hash
        const newData = new Uint8Array(hashObject.data.length + arrayBuffer.byteLength);
        newData.set(hashObject.data);
        newData.set(new Uint8Array(arrayBuffer), hashObject.data.length);
        hashObject.data = newData;

        offset += chunkSize;

        if (onProgress) {
            const percentage = (offset / file.size) * 100;
            onProgress(Math.min(percentage, 100));
        }
    }

    // Final hash calculation
    const hashBuffer = await crypto.subtle.digest('SHA-256', hashObject.data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    const hashHex = hashArray
        .map(b => b.toString(16).padStart(2, '0'))
        .join('');

    return hashHex.toLowerCase() === expectedChecksum.toLowerCase();
}
```

## Corruption Detection

### Identify Corruption Types

```python
def diagnose_file_corruption(
    file_path: Path,
    expected_checksum: str,
    expected_size: int
) -> Dict[str, any]:
    """Diagnose types of file corruption."""
    diagnosis = {
        'file_exists': file_path.exists(),
        'checksum_valid': False,
        'size_correct': False,
        'error_type': None,
        'details': {}
    }

    if not file_path.exists():
        diagnosis['error_type'] = 'missing_file'
        return diagnosis

    # Check file size
    actual_size = file_path.stat().st_size
    if actual_size != expected_size:
        diagnosis['size_correct'] = False
        diagnosis['error_type'] = 'size_mismatch'
        diagnosis['details'] = {
            'expected': expected_size,
            'actual': actual_size,
            'difference': abs(expected_size - actual_size)
        }
    else:
        diagnosis['size_correct'] = True

    # Check checksum
    actual_checksum = calculate_sha256(file_path)
    if actual_checksum.lower() == expected_checksum.lower():
        diagnosis['checksum_valid'] = True
    else:
        diagnosis['checksum_valid'] = False
        if diagnosis['error_type'] is None:
            diagnosis['error_type'] = 'checksum_mismatch'

        diagnosis['details']['expected_checksum'] = expected_checksum
        diagnosis['details']['actual_checksum'] = actual_checksum

    return diagnosis

# Usage
result = diagnose_file_corruption(
    Path("model.bin"),
    "expected_hash_here",
    expected_size=10737418240  # 10GB
)

if result['error_type'] == 'size_mismatch':
    print(f"Incomplete download: missing {result['details']['difference']} bytes")
elif result['error_type'] == 'checksum_mismatch':
    print("File corrupted during transfer")
```

## Automated Cleanup

### Remove Corrupted Files

```rust
pub fn cleanup_corrupted_models(
    cache_dir: &Path,
    model_registry: &HashMap<String, ModelMetadata>,
) -> Result<CleanupReport, Box<dyn std::error::Error>> {
    let mut removed_files = Vec::new();
    let mut removed_bytes = 0u64;

    for entry in fs::read_dir(cache_dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_name = path.file_name().unwrap().to_string_lossy();

        if let Some(metadata) = model_registry.get(file_name.as_ref()) {
            if let Ok(is_valid) = verify_file_checksum(&path, &metadata.checksum) {
                if !is_valid {
                    let size = entry.metadata()?.len();
                    removed_bytes += size;
                    fs::remove_file(&path)?;
                    removed_files.push(file_name.to_string());
                }
            }
        }
    }

    Ok(CleanupReport {
        removed_files,
        removed_bytes,
        timestamp: std::time::SystemTime::now(),
    })
}
```

## Registry with Checksums

### Model Registry Structure

```json
{
  "models": [
    {
      "id": "llama2-7b",
      "name": "Llama 2 7B",
      "version": "1.0",
      "url": "https://huggingface.co/...",
      "sha256": "abc123def456...",
      "size": 14000000000,
      "size_gb": 13.04,
      "format": "gguf",
      "quantization": "q4_k_m"
    },
    {
      "id": "stable-diffusion-2",
      "name": "Stable Diffusion 2.1",
      "version": "2.1",
      "url": "https://huggingface.co/...",
      "sha256": "xyz789abc123...",
      "size": 7700000000,
      "size_gb": 7.18,
      "format": "safetensors"
    }
  ]
}
```

## Verification Workflow

### Complete Verification Process

```rust
pub async fn download_and_verify_model(
    url: &str,
    cache_dir: &Path,
    expected_checksum: &str,
    window: &tauri::Window,
) -> Result<PathBuf, Box<dyn std::error::Error>> {
    let file_path = cache_dir.join("temp_download.bin");

    // Step 1: Download
    window.emit("status", "Downloading model...")?;
    download_model(url, &file_path, window).await?;

    // Step 2: Verify
    window.emit("status", "Verifying integrity...")?;
    if !verify_file_checksum(&file_path, expected_checksum)? {
        fs::remove_file(&file_path)?;
        return Err("Checksum validation failed".into());
    }

    // Step 3: Finalize
    window.emit("status", "Model ready")?;
    let final_path = cache_dir.join("model.bin");
    fs::rename(&file_path, &final_path)?;

    Ok(final_path)
}
```

## Best Practices

1. **Always Verify** - Check every downloaded model before use
2. **Store Checksums Securely** - Use version control or signed manifests
3. **Display Progress** - Show verification progress for large files
4. **Handle Failures** - Provide clear error messages for corruption
5. **Automatic Cleanup** - Remove corrupted files automatically
6. **Log Verification** - Track which models were verified and when
7. **Support Multiple Checksums** - Consider SHA256 + CRC32 for redundancy
8. **Document Process** - Help users understand why verification is important

## Performance Optimization

### Parallel Verification

```rust
use rayon::prelude::*;

pub fn verify_multiple_models(
    models: Vec<(&Path, &str)>,
) -> Vec<Result<bool, String>> {
    models
        .par_iter()
        .map(|(path, checksum)| {
            verify_file_checksum(path, checksum)
                .map_err(|e| e.to_string())
        })
        .collect()
}
```

### Incremental Verification

```python
def verify_by_chunks(
    file_path: Path,
    expected_checksum: str,
    chunk_size: int = 50 * 1024 * 1024  # 50MB chunks
) -> bool:
    """Verify large files in chunks without loading entire file."""
    hasher = hashlib.sha256()

    with open(file_path, 'rb') as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            hasher.update(chunk)

    return hasher.hexdigest().lower() == expected_checksum.lower()
```

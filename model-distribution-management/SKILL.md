---
name: model-distribution-management
description: Manage large model file distribution (7-20GB) using Tauri resources and on-demand downloading. Use when bundling models with installers, implementing progressive downloads with checksum validation, managing platform-specific cache locations, or verifying model integrity for desktop AI applications.
---

# Model Distribution & Asset Management

## Overview

This skill enables efficient distribution and management of large model files (7-20GB) in Tauri-based desktop applications. It provides strategies for bundling models with installers, implementing on-demand progressive downloads, validating integrity through checksums, and managing platform-specific cache locations across Windows, macOS, and Linux.

## Core Capabilities

### 1. Tauri Asset Protocol for Bundled Models
Bundle pre-downloaded models directly into application installers for immediate offline access. Use the `asset://` protocol to reference bundled models without file system paths, configure resource embedding in `tauri.conf.json`, and optimize application size through intelligent model selection.

### 2. On-Demand Download Strategies
Implement progressive/incremental downloads for large models without blocking the UI. Queue multiple model downloads by priority, resume interrupted downloads from checkpoints, and provide background downloading capabilities while users work.

### 3. Platform-Specific Cache Locations
Automatically manage cache directories across operating systems:
- **Windows:** `%APPDATA%\{AppName}\cache\models`
- **macOS:** `~/Library/Application Support/{AppName}/cache/models`
- **Linux:** `~/.config/{AppName}/cache/models` (or `$XDG_CACHE_HOME/{AppName}/models`)

### 4. SHA256 Checksum Validation
Verify downloaded models against checksums to detect corruption or tampering. Generate checksums during model preparation, validate downloads before use, and automatically clean up corrupted files.

### 5. Resumable Downloads with Progress
Stream model downloads with byte-level tracking, display real-time UI feedback (percentage, MB/s, estimated time), save download state for resumption after interruptions, and handle network errors with retry logic.

### 6. Model Registry and Metadata Management
Maintain a central registry of available models with metadata (name, version, size, URLs, checksums). Track model versions, manage updates, and support multiple model variants for different hardware configurations.

### 7. Integrity Verification
Verify models before use to detect file corruption, validate model format and structure, and implement automated cleanup of corrupted files with corruption reporting.

## Workflow Decision Tree

```
START: Need to distribute models?
├─ Models < 100MB → Embed in installer
├─ Models 100MB-1GB → Use asset:// protocol with installer
├─ Models 1GB-5GB → On-demand download with progress UI
└─ Models > 5GB → Resumable download + checksum validation
```

## Key Tasks

### Task 1: Bundle Models with Installers
Reference `tauri-asset-protocol.md` and `model-registry.json` to configure bundled model distribution. Use the Tauri asset protocol for fast local access without requiring external downloads.

**When to use:** Delivering complete applications with pre-downloaded models for offline-first use cases.

### Task 2: Implement Progressive Downloads
Use `download-model-with-progress.py` script with the on-demand-download reference guide to download large models incrementally. Implement resumable downloads that can be paused and resumed without re-downloading.

**When to use:** Models exceed 1GB, users have limited bandwidth, or network interruptions are likely.

### Task 3: Validate Model Integrity
Execute `verify-model-integrity.py` script with SHA256 checksums from `model-registry.json` to verify downloaded files. Run verification before using models in inference pipelines.

**When to use:** After downloading models, before first use, or periodically for cached models.

### Task 4: Manage Platform-Specific Caches
Reference `platform-specific-paths.md` for cache directory configuration. Implement cross-platform cache management that respects OS conventions and user preferences.

**When to use:** Building desktop applications targeting Windows, macOS, and Linux simultaneously.

## Best Practices

1. **Always validate checksums** after downloads to detect corruption
2. **Use resumable downloads** for files larger than 500MB to handle network interruptions
3. **Implement exponential backoff** for failed download attempts
4. **Clean up orphaned cache files** periodically to manage disk space
5. **Store model registry** in version control for reproducibility
6. **Provide user feedback** during downloads and verification operations
7. **Test across all platforms** before release to verify cache paths work correctly
8. **Monitor cache size** to warn users when models consume excessive disk space

## Implementation Example

```typescript
// Tauri command for downloading models with progress
#[tauri::command]
async fn download_model(
    model_id: String,
    on_progress: impl Fn(u64, u64) + Send + 'static
) -> Result<String, String> {
    // 1. Get model metadata from registry
    // 2. Create cache directory (platform-specific)
    // 3. Download model with progress tracking
    // 4. Verify checksum
    // 5. Return cache path
}
```

## Resources

This skill includes comprehensive resources for model distribution management:

### scripts/
Executable Python scripts for automation and operations:
- `download-model-with-progress.py` - Resumable downloads with UI progress integration
- `verify-model-integrity.py` - Checksum validation and corruption detection

### references/
Detailed technical documentation and guides:
- `tauri-asset-protocol.md` - Bundling resources and asset:// URL handling
- `on-demand-download.md` - Progressive download implementation patterns
- `platform-specific-paths.md` - Cache locations and path configuration per OS
- `integrity-verification.md` - SHA256 checksums and file validation

### assets/
Configuration files and templates:
- `model-registry.json` - Model metadata, URLs, versions, and checksums

## Related Skills

- Tauri desktop application architecture
- AI model management and versioning
- File system operations and cross-platform APIs
- Data integrity, security, and checksums

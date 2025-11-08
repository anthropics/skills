# On-Demand Download Strategy

## Overview

Progressive on-demand downloading enables users to access applications immediately while models download in the background. This approach is essential for 7-20GB models that are impractical to include in installers.

## Download Architecture

### Phase 1: Pre-Download Check
Before user interacts with AI features, check if model is available:

```rust
#[tauri::command]
async fn check_model_available(
    model_id: String,
    cache_dir: String,
) -> Result<bool, String> {
    let model_path = Path::new(&cache_dir).join(&format!("{}.bin", model_id));
    Ok(model_path.exists())
}
```

### Phase 2: Initiate Download
If model unavailable, start download:

```rust
#[tauri::command]
async fn start_model_download(
    model_id: String,
    url: String,
    cache_dir: String,
    window: tauri::Window,
) -> Result<String, String> {
    // Create cache directory if missing
    let cache_path = Path::new(&cache_dir);
    fs::create_dir_all(cache_path).map_err(|e| e.to_string())?;

    // Spawn download task
    let window_clone = window.clone();
    tokio::spawn(async move {
        if let Err(e) = download_model_with_progress(
            &url,
            cache_path,
            &window_clone
        ).await {
            let _ = window_clone.emit("download_error", e.to_string());
        }
    });

    Ok(format!("Download started for {}", model_id))
}
```

### Phase 3: Stream Download
Use streaming downloads for large files to avoid memory issues:

```rust
use reqwest::Client;
use std::fs::File;
use std::io::Write;
use tokio::io::AsyncWriteExt;

async fn download_model_with_progress(
    url: &str,
    cache_dir: &Path,
    window: &tauri::Window,
) -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    let response = client.get(url).send().await?;

    let total_size = response.content_length().unwrap_or(0);
    let mut downloaded: u64 = 0;

    let model_path = cache_dir.join("model.bin");
    let mut file = File::create(&model_path)?;

    let mut stream = response.bytes_stream();
    use futures_util::StreamExt;

    while let Some(chunk) = stream.next().await {
        let chunk = chunk?;
        downloaded += chunk.len() as u64;

        // Write to file
        file.write_all(&chunk)?;

        // Emit progress event
        let percentage = (downloaded as f64 / total_size as f64) * 100.0;
        window.emit("download_progress", DownloadProgress {
            downloaded,
            total: total_size,
            percentage,
        })?;
    }

    Ok(())
}
```

## Frontend Progress Display

### React Component Example

```typescript
import React, { useState, useEffect } from 'react';
import { invoke, event } from '@tauri-apps/api/tauri';

interface DownloadProgress {
    downloaded: number;
    total: number;
    percentage: number;
}

export function ModelDownload({ modelId }: { modelId: string }) {
    const [progress, setProgress] = useState<DownloadProgress | null>(null);
    const [status, setStatus] = useState<'idle' | 'downloading' | 'complete' | 'error'>('idle');

    useEffect(() => {
        // Listen for download progress events
        const unlisten = event.listen<DownloadProgress>(
            'download_progress',
            (event) => {
                setProgress(event.payload);
            }
        );

        return () => {
            unlisten.then(fn => fn());
        };
    }, []);

    const handleDownload = async () => {
        try {
            setStatus('downloading');
            await invoke('start_model_download', {
                modelId,
                url: `https://example.com/models/${modelId}.bin`,
                cacheDir: '/path/to/cache',
            });
        } catch (error) {
            setStatus('error');
            console.error('Download failed:', error);
        }
    };

    const formatSize = (bytes: number) => {
        const gb = bytes / (1024 * 1024 * 1024);
        return gb.toFixed(2);
    };

    return (
        <div className="download-container">
            {status === 'idle' && (
                <button onClick={handleDownload}>Download Model</button>
            )}

            {status === 'downloading' && progress && (
                <div>
                    <p>Downloading... {progress.percentage.toFixed(1)}%</p>
                    <progress value={progress.percentage} max={100} />
                    <p>
                        {formatSize(progress.downloaded)} / {formatSize(progress.total)} GB
                    </p>
                </div>
            )}

            {status === 'error' && <p>Download failed</p>}
            {status === 'complete' && <p>Download complete!</p>}
        </div>
    );
}
```

## Resumable Downloads

### Save Download State

```rust
use serde::{Deserialize, Serialize};
use std::fs;

#[derive(Serialize, Deserialize)]
struct DownloadState {
    model_id: String,
    url: String,
    downloaded_bytes: u64,
    total_bytes: u64,
    checksum: String,
    timestamp: i64,
}

fn save_download_state(
    cache_dir: &Path,
    state: &DownloadState,
) -> Result<(), Box<dyn std::error::Error>> {
    let state_file = cache_dir.join("download_state.json");
    let json = serde_json::to_string(state)?;
    fs::write(state_file, json)?;
    Ok(())
}

fn load_download_state(
    cache_dir: &Path,
) -> Result<Option<DownloadState>, Box<dyn std::error::Error>> {
    let state_file = cache_dir.join("download_state.json");
    if !state_file.exists() {
        return Ok(None);
    }
    let json = fs::read_to_string(state_file)?;
    Ok(Some(serde_json::from_str(&json)?))
}
```

### Resume from Checkpoint

```rust
async fn resume_download(
    url: &str,
    cache_dir: &Path,
    window: &tauri::Window,
) -> Result<(), Box<dyn std::error::Error>> {
    // Load previous state
    if let Some(state) = load_download_state(cache_dir)? {
        // Verify the URL matches
        if state.url != url {
            return Err("URL mismatch, cannot resume".into());
        }

        // Resume from downloaded_bytes
        let client = Client::new();
        let response = client
            .get(url)
            .header("Range", format!("bytes={}-", state.downloaded_bytes))
            .send()
            .await?;

        // Continue downloading from checkpoint
        resume_download_stream(response, cache_dir, window, state).await?;
    }

    Ok(())
}
```

## Priority Queue Management

### Download Queue Implementation

```rust
use async_priority_queue::AsyncPriorityQueue;
use std::cmp::Ordering;

#[derive(Clone)]
struct DownloadTask {
    model_id: String,
    url: String,
    priority: u32,
}

impl Eq for DownloadTask {}

impl PartialEq for DownloadTask {
    fn eq(&self, other: &Self) -> bool {
        self.model_id == other.model_id
    }
}

impl Ord for DownloadTask {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority.cmp(&self.priority) // Reverse for max-heap
    }
}

impl PartialOrd for DownloadTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub struct DownloadQueue {
    queue: AsyncPriorityQueue<DownloadTask>,
    active_downloads: Arc<Mutex<HashSet<String>>>,
}

impl DownloadQueue {
    pub async fn add_task(&self, task: DownloadTask) {
        self.queue.push(task).await;
    }

    pub async fn get_next_task(&self) -> Option<DownloadTask> {
        self.queue.pop().await
    }
}
```

## Error Handling and Retry

### Exponential Backoff Retry

```rust
async fn download_with_retry(
    url: &str,
    cache_dir: &Path,
    window: &tauri::Window,
    max_retries: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut retry_count = 0;
    let mut backoff_ms = 1000; // Start with 1 second

    loop {
        match download_model_with_progress(url, cache_dir, window).await {
            Ok(_) => return Ok(()),
            Err(e) if retry_count < max_retries => {
                retry_count += 1;
                window.emit(
                    "download_retry",
                    format!("Retry {} of {}", retry_count, max_retries),
                )?;

                // Exponential backoff: 1s, 2s, 4s, 8s...
                tokio::time::sleep(
                    tokio::time::Duration::from_millis(backoff_ms)
                ).await;

                backoff_ms = std::cmp::min(backoff_ms * 2, 60000); // Max 60 seconds
            }
            Err(e) => return Err(e),
        }
    }
}
```

## Network Detection

### Check Network Availability

```rust
#[tauri::command]
async fn check_network_available() -> Result<bool, String> {
    // Simple HTTP HEAD request to reliable endpoint
    match reqwest::Client::new()
        .head("https://www.google.com")
        .timeout(std::time::Duration::from_secs(5))
        .send()
        .await {
        Ok(_) => Ok(true),
        Err(_) => Ok(false),
    }
}

#[tauri::command]
fn is_download_paused() -> Result<bool, String> {
    // Check if download was manually paused
    // Return pause state from app state
    Ok(false)
}
```

## Background Download Service

### Tauri State Management

```rust
use tauri::State;
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct DownloadManager {
    downloads: Arc<Mutex<HashMap<String, DownloadTask>>>,
    queue: Arc<Mutex<Vec<DownloadTask>>>,
}

#[tauri::command]
async fn queue_model_download(
    model_id: String,
    download_manager: State<'_, DownloadManager>,
) -> Result<String, String> {
    let mut downloads = download_manager.downloads.lock().await;
    if !downloads.contains_key(&model_id) {
        downloads.insert(
            model_id.clone(),
            DownloadTask {
                model_id: model_id.clone(),
                url: "".to_string(),
                priority: 1,
            },
        );
        Ok(format!("Queued {}", model_id))
    } else {
        Err("Already downloading".to_string())
    }
}
```

## Best Practices

1. **Progressive Feedback** - Update UI every 100-500MB chunk
2. **Pause/Resume** - Allow users to pause downloads and resume later
3. **Network Detection** - Check connectivity before starting
4. **Partial File Cleanup** - Remove incomplete downloads on cancellation
5. **Bandwidth Limiting** - Allow users to set bandwidth caps
6. **Scheduled Downloads** - Download during off-peak hours if configured
7. **Prioritization** - Essential models download first
8. **Integrity Check** - Verify checksums after download completes

## Performance Metrics

Monitor download performance:

```rust
#[derive(Serialize)]
struct DownloadMetrics {
    average_speed_mbps: f64,
    time_elapsed_secs: u64,
    bytes_downloaded: u64,
    estimated_time_remaining_secs: u64,
}
```

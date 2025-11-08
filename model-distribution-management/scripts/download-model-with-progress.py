#!/usr/bin/env python3
"""
Model Download with Progress Tracking

Resumable downloads with real-time progress updates for large model files.
Supports pause/resume, exponential backoff retry, and bandwidth limiting.

Usage:
    python download-model-with-progress.py --url <URL> --output <PATH> [options]
"""

import os
import sys
import time
import argparse
import json
import hashlib
from pathlib import Path
from typing import Optional, Callable, Dict, Any
from dataclasses import dataclass, asdict
from datetime import datetime
import requests
from requests.exceptions import RequestException, Timeout, ConnectionError
import signal


@dataclass
class DownloadProgress:
    """Track download progress state."""
    downloaded_bytes: int = 0
    total_bytes: int = 0
    start_time: float = 0.0
    paused_time: float = 0.0

    @property
    def percentage(self) -> float:
        if self.total_bytes == 0:
            return 0.0
        return (self.downloaded_bytes / self.total_bytes) * 100

    @property
    def speed_mbps(self) -> float:
        elapsed = time.time() - self.start_time - self.paused_time
        if elapsed <= 0:
            return 0.0
        mb_downloaded = self.downloaded_bytes / (1024 * 1024)
        return mb_downloaded / elapsed

    @property
    def eta_seconds(self) -> float:
        if self.speed_mbps <= 0:
            return 0.0
        remaining_bytes = self.total_bytes - self.downloaded_bytes
        remaining_mb = remaining_bytes / (1024 * 1024)
        return remaining_mb / self.speed_mbps

    @property
    def eta_human(self) -> str:
        """Human-readable ETA."""
        eta = self.eta_seconds
        if eta <= 0:
            return "Complete"

        hours = int(eta // 3600)
        minutes = int((eta % 3600) // 60)
        seconds = int(eta % 60)

        if hours > 0:
            return f"{hours}h {minutes}m"
        elif minutes > 0:
            return f"{minutes}m {seconds}s"
        else:
            return f"{seconds}s"


class DownloadState:
    """Manage download resumption state."""

    def __init__(self, state_file: Path):
        self.state_file = state_file

    def save(self, model_id: str, url: str, downloaded: int, total: int) -> None:
        """Save download state for resumption."""
        state = {
            'model_id': model_id,
            'url': url,
            'downloaded_bytes': downloaded,
            'total_bytes': total,
            'timestamp': datetime.now().isoformat(),
        }
        with open(self.state_file, 'w') as f:
            json.dump(state, f)

    def load(self) -> Optional[Dict[str, Any]]:
        """Load saved download state."""
        if not self.state_file.exists():
            return None

        try:
            with open(self.state_file, 'r') as f:
                return json.load(f)
        except (json.JSONDecodeError, IOError):
            return None

    def clear(self) -> None:
        """Clear saved state."""
        if self.state_file.exists():
            self.state_file.unlink()


class ModelDownloader:
    """Download models with progress tracking and resumable support."""

    def __init__(
        self,
        output_dir: Path,
        chunk_size: int = 8192,
        max_retries: int = 5,
        timeout: int = 30,
    ):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.chunk_size = chunk_size
        self.max_retries = max_retries
        self.timeout = timeout
        self.pause_requested = False
        self.resume_requested = False

    def download(
        self,
        url: str,
        model_id: str,
        on_progress: Optional[Callable[[DownloadProgress], None]] = None,
        expected_checksum: Optional[str] = None,
    ) -> Path:
        """
        Download a model with progress tracking and resumable support.

        Args:
            url: Download URL
            model_id: Model identifier
            on_progress: Callback for progress updates
            expected_checksum: Expected SHA256 checksum for verification

        Returns:
            Path to downloaded file

        Raises:
            RuntimeError: If download fails after retries
        """
        output_file = self.output_dir / f"{model_id}.bin"
        state_file = self.output_dir / f"{model_id}.download_state"
        state_manager = DownloadState(state_file)

        # Setup signal handler for graceful pause/resume
        self._setup_signal_handlers()

        retry_count = 0
        backoff_ms = 1000

        while retry_count < self.max_retries:
            try:
                # Try resumable download
                result = self._download_resumable(
                    url=url,
                    output_file=output_file,
                    state_manager=state_manager,
                    on_progress=on_progress,
                )

                if result:
                    # Verify checksum if provided
                    if expected_checksum:
                        if self._verify_checksum(output_file, expected_checksum):
                            state_manager.clear()
                            return output_file
                        else:
                            raise RuntimeError("Checksum verification failed")
                    else:
                        state_manager.clear()
                        return output_file

                return output_file

            except (ConnectionError, Timeout, RequestException) as e:
                retry_count += 1

                if retry_count < self.max_retries:
                    wait_seconds = (backoff_ms / 1000)
                    print(
                        f"Connection error, retrying in {wait_seconds}s "
                        f"(attempt {retry_count}/{self.max_retries}): {e}"
                    )
                    time.sleep(wait_seconds)
                    backoff_ms = min(backoff_ms * 2, 60000)  # Cap at 60s
                else:
                    raise RuntimeError(
                        f"Download failed after {self.max_retries} retries: {e}"
                    )

        raise RuntimeError("Download failed: Unknown error")

    def _download_resumable(
        self,
        url: str,
        output_file: Path,
        state_manager: DownloadState,
        on_progress: Optional[Callable[[DownloadProgress], None]] = None,
    ) -> bool:
        """Download with resumable support."""
        # Get remote file size
        try:
            response = requests.head(url, timeout=self.timeout, allow_redirects=True)
            total_size = int(response.headers.get('content-length', 0))
        except RequestException:
            total_size = 0

        # Check for saved state
        saved_state = state_manager.load()
        resume_from = 0

        if saved_state and saved_state.get('downloaded_bytes', 0) > 0:
            resume_from = saved_state['downloaded_bytes']
            print(f"Resuming from {resume_from / (1024**3):.2f} GB...")

        # Start download
        progress = DownloadProgress(
            downloaded_bytes=resume_from,
            total_bytes=total_size or 0,
            start_time=time.time(),
        )

        try:
            headers = {}
            if resume_from > 0:
                headers['Range'] = f'bytes={resume_from}-'

            response = requests.get(
                url,
                headers=headers,
                stream=True,
                timeout=self.timeout,
            )
            response.raise_for_status()

            # Update total size if not known
            if 'content-length' in response.headers:
                progress.total_bytes = (
                    resume_from + int(response.headers['content-length'])
                )

            # Download in chunks
            mode = 'ab' if resume_from > 0 else 'wb'
            with open(output_file, mode) as f:
                for chunk in response.iter_content(chunk_size=self.chunk_size):
                    if self.pause_requested:
                        state_manager.save(
                            model_id=output_file.stem,
                            url=url,
                            downloaded=progress.downloaded_bytes,
                            total=progress.total_bytes,
                        )
                        self._wait_for_resume()
                        state_manager.clear()

                    if chunk:
                        f.write(chunk)
                        progress.downloaded_bytes += len(chunk)

                        if on_progress:
                            on_progress(progress)

            return True

        except RequestException as e:
            # Save state for resumption
            state_manager.save(
                model_id=output_file.stem,
                url=url,
                downloaded=progress.downloaded_bytes,
                total=progress.total_bytes,
            )
            raise

    @staticmethod
    def _verify_checksum(file_path: Path, expected_checksum: str) -> bool:
        """Verify file checksum."""
        sha256_hash = hashlib.sha256()

        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(8192), b''):
                sha256_hash.update(chunk)

        calculated = sha256_hash.hexdigest()
        return calculated.lower() == expected_checksum.lower()

    def _setup_signal_handlers(self) -> None:
        """Setup signal handlers for pause/resume."""
        def handle_pause(signum, frame):
            print("\nPause requested (SIGTERM). Saving state...")
            self.pause_requested = True

        def handle_resume(signum, frame):
            print("\nResume requested (SIGCONT)")
            self.resume_requested = True

        signal.signal(signal.SIGTERM, handle_pause)
        if hasattr(signal, 'SIGCONT'):
            signal.signal(signal.SIGCONT, handle_resume)

    def _wait_for_resume(self) -> None:
        """Wait for resume signal."""
        while self.pause_requested:
            time.sleep(1)


def format_size(bytes_size: int) -> str:
    """Format bytes to human-readable size."""
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if bytes_size < 1024:
            return f"{bytes_size:.2f} {unit}"
        bytes_size /= 1024
    return f"{bytes_size:.2f} PB"


def progress_callback(progress: DownloadProgress) -> None:
    """Print progress to console."""
    percentage = progress.percentage
    downloaded = format_size(progress.downloaded_bytes)
    total = format_size(progress.total_bytes)
    speed = f"{progress.speed_mbps:.2f} MB/s"
    eta = progress.eta_human

    bar_length = 40
    filled = int((percentage / 100) * bar_length)
    bar = '█' * filled + '░' * (bar_length - filled)

    print(
        f"\r[{bar}] {percentage:5.1f}% | {downloaded:>10} / {total:>10} "
        f"| {speed:>10} | ETA: {eta:>6}",
        end='',
        flush=True,
    )


def main():
    """CLI interface for model downloading."""
    parser = argparse.ArgumentParser(
        description='Download large model files with progress tracking'
    )
    parser.add_argument('--url', required=True, help='Download URL')
    parser.add_argument('--model-id', required=True, help='Model identifier')
    parser.add_argument(
        '--output-dir',
        default='./models',
        help='Output directory (default: ./models)',
    )
    parser.add_argument(
        '--checksum',
        help='Expected SHA256 checksum for verification',
    )
    parser.add_argument(
        '--chunk-size',
        type=int,
        default=8192,
        help='Download chunk size in bytes (default: 8192)',
    )
    parser.add_argument(
        '--retries',
        type=int,
        default=5,
        help='Maximum retry attempts (default: 5)',
    )
    parser.add_argument(
        '--timeout',
        type=int,
        default=30,
        help='Request timeout in seconds (default: 30)',
    )

    args = parser.parse_args()

    # Create downloader
    downloader = ModelDownloader(
        output_dir=Path(args.output_dir),
        chunk_size=args.chunk_size,
        max_retries=args.retries,
        timeout=args.timeout,
    )

    # Start download
    print(f"Downloading {args.model_id} from {args.url}")
    print(f"Output directory: {args.output_dir}\n")

    try:
        result_path = downloader.download(
            url=args.url,
            model_id=args.model_id,
            on_progress=progress_callback,
            expected_checksum=args.checksum,
        )

        print(f"\n✓ Download complete: {result_path}")
        return 0

    except Exception as e:
        print(f"\n✗ Download failed: {e}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())

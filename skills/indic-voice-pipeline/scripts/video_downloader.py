#!/usr/bin/env python3
"""Video Downloader — Download videos, audio, and playlists from any URL.

Commands:
    download  — Download single video (best quality MP4)
    audio     — Download audio only (MP3/M4A/Opus)
    playlist  — Download all videos in a playlist
    formats   — List available formats/qualities for a URL
    info      — Show video metadata without downloading

Examples:
    python video_downloader.py download "https://youtube.com/watch?v=..."
    python video_downloader.py audio "https://youtube.com/watch?v=..." --audio-format m4a
    python video_downloader.py playlist "https://youtube.com/playlist?list=..."
    python video_downloader.py formats "https://youtube.com/watch?v=..."
    python video_downloader.py info "https://youtube.com/watch?v=..."
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


# ─── HELPERS ────────────────────────────────────────────────────────────────────


def _timestamp_str(seconds: float | int | None) -> str:
    """Convert seconds to HH:MM:SS or MM:SS."""
    if not seconds:
        return "00:00"
    seconds = float(seconds)
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    s = int(seconds % 60)
    return f"{h:02d}:{m:02d}:{s:02d}" if h > 0 else f"{m:02d}:{s:02d}"


def _get_format_string(quality: str | None) -> str:
    """Get yt-dlp format string for desired quality."""
    if not quality:
        return "bestvideo[height<=1080][ext=mp4]+bestaudio[ext=m4a]/best[height<=1080][ext=mp4]/best"

    q = str(quality).lower().replace("p", "")
    if q == "4k":
        q = "2160"
    try:
        height = int(q)
        return f"bestvideo[height<={height}][ext=mp4]+bestaudio[ext=m4a]/best[height<={height}][ext=mp4]/best"
    except ValueError:
        return "best[ext=mp4]/best"


def _find_downloaded_file(directory: Path, extensions: list[str]) -> Path | None:
    """Find the most recently created file with given extensions."""
    candidates = []
    for ext in extensions:
        candidates.extend(directory.glob(f"*{ext}"))
    if not candidates:
        return None
    return max(candidates, key=lambda p: p.stat().st_mtime)


def _check_ytdlp() -> dict | None:
    """Check yt-dlp is available. Returns error dict if not."""
    try:
        subprocess.run(["yt-dlp", "--version"], capture_output=True, check=True)
        return None
    except (FileNotFoundError, subprocess.CalledProcessError):
        return {"error": "yt-dlp not found. Install with: pip install yt-dlp"}


def _get_metadata(url: str, playlist: bool = False) -> tuple[dict | None, dict | None]:
    """Fetch metadata from URL. Returns (metadata, error)."""
    meta_cmd = ["yt-dlp", "--dump-json", "--no-download"]
    if not playlist:
        meta_cmd.append("--no-playlist")
    meta_cmd.append(url)

    result = subprocess.run(meta_cmd, capture_output=True, text=True)
    if result.returncode != 0:
        return None, {"error": f"Failed to get video metadata: {result.stderr.strip()[:500]}"}

    try:
        meta = json.loads(result.stdout.strip().splitlines()[0])
        return meta, None
    except (json.JSONDecodeError, IndexError):
        return None, {"error": "Failed to parse video metadata"}


def _format_filesize(size_bytes: int | float | None) -> str:
    """Human-readable file size."""
    if not size_bytes:
        return "unknown"
    size = float(size_bytes)
    for unit in ["B", "KB", "MB", "GB"]:
        if size < 1024:
            return f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} TB"


def _save_meta(data: dict, output_dir: Path) -> None:
    """Save download_meta.json alongside the download."""
    meta_path = output_dir / "download_meta.json"
    with open(meta_path, "w") as f:
        json.dump(data, f, indent=2)


def _build_metadata_dict(meta: dict, url: str) -> dict:
    """Build a standard metadata dict from yt-dlp JSON."""
    return {
        "title": meta.get("title", "Unknown"),
        "uploader": meta.get("uploader", "Unknown"),
        "upload_date": meta.get("upload_date", ""),
        "duration_seconds": meta.get("duration", 0),
        "duration": _timestamp_str(meta.get("duration", 0)),
        "view_count": meta.get("view_count"),
        "like_count": meta.get("like_count"),
        "description": (meta.get("description") or "")[:500],
        "webpage_url": meta.get("webpage_url", url),
        "resolution": f"{meta.get('width', '?')}x{meta.get('height', '?')}",
        "thumbnail": meta.get("thumbnail", ""),
    }


# ─── COMMANDS ───────────────────────────────────────────────────────────────────


def cmd_download(
    url: str,
    output_dir: str = "~/Downloads",
    quality: str | None = None,
    format_id: str | None = None,
    extract_subs: bool = True,
) -> dict:
    """Download a single video from URL."""
    err = _check_ytdlp()
    if err:
        return err

    out_path = Path(output_dir).expanduser()
    out_path.mkdir(parents=True, exist_ok=True)

    print("Fetching metadata...", file=sys.stderr)
    meta, err = _get_metadata(url)
    if err:
        return err

    video_template = str(out_path / "%(title).80s.%(ext)s")

    if format_id:
        fmt = format_id
    else:
        fmt = _get_format_string(quality)

    dl_cmd = [
        "yt-dlp",
        "-f", fmt,
        "--merge-output-format", "mp4",
        "-o", video_template,
        "--no-playlist",
        "--no-overwrites",
    ]

    if extract_subs:
        dl_cmd.extend([
            "--write-subs",
            "--write-auto-subs",
            "--sub-langs", "en",
            "--sub-format", "srt/vtt/best",
            "--convert-subs", "srt",
        ])

    dl_cmd.append(url)

    print("Downloading...", file=sys.stderr)
    dl_result = subprocess.run(dl_cmd, capture_output=True, text=True)

    if dl_result.returncode != 0:
        # Fallback: simpler format
        print("Retrying with fallback format...", file=sys.stderr)
        dl_cmd_simple = [
            "yt-dlp",
            "-f", "best[ext=mp4]/best",
            "-o", video_template,
            "--no-playlist",
            "--no-overwrites",
            url,
        ]
        dl_result = subprocess.run(dl_cmd_simple, capture_output=True, text=True)
        if dl_result.returncode != 0:
            return {"error": f"Download failed: {dl_result.stderr.strip()[:500]}"}

    video_file = _find_downloaded_file(out_path, [".mp4", ".mkv", ".webm", ".mov"])
    if not video_file:
        return {"error": f"Download completed but video file not found in {out_path}"}

    sub_file = _find_downloaded_file(out_path, [".srt", ".vtt"])

    file_size = video_file.stat().st_size

    result = {
        "status": "downloaded",
        "video_path": str(video_file),
        "video_filename": video_file.name,
        "file_size": _format_filesize(file_size),
        "file_size_bytes": file_size,
        "output_dir": str(out_path),
        "metadata": _build_metadata_dict(meta, url),
    }

    if sub_file:
        result["subtitle_path"] = str(sub_file)
        result["subtitle_filename"] = sub_file.name

    _save_meta(result, out_path)
    return result


def cmd_audio(
    url: str,
    output_dir: str = "~/Downloads",
    audio_format: str = "mp3",
) -> dict:
    """Download audio only from URL."""
    err = _check_ytdlp()
    if err:
        return err

    out_path = Path(output_dir).expanduser()
    out_path.mkdir(parents=True, exist_ok=True)

    print("Fetching metadata...", file=sys.stderr)
    meta, err = _get_metadata(url)
    if err:
        return err

    audio_template = str(out_path / "%(title).80s.%(ext)s")
    dl_cmd = [
        "yt-dlp",
        "-x",
        "--audio-format", audio_format,
        "--audio-quality", "0",
        "-o", audio_template,
        "--no-playlist",
        "--no-overwrites",
        url,
    ]

    print("Downloading audio...", file=sys.stderr)
    dl_result = subprocess.run(dl_cmd, capture_output=True, text=True)
    if dl_result.returncode != 0:
        return {"error": f"Audio download failed: {dl_result.stderr.strip()[:500]}"}

    ext_map = {"mp3": [".mp3"], "m4a": [".m4a"], "opus": [".opus"]}
    search_exts = ext_map.get(audio_format, [f".{audio_format}"])
    # Also search common fallbacks
    search_exts.extend([".mp3", ".m4a", ".opus", ".ogg", ".webm"])

    audio_file = _find_downloaded_file(out_path, search_exts)
    if not audio_file:
        return {"error": f"Download completed but audio file not found in {out_path}"}

    file_size = audio_file.stat().st_size

    result = {
        "status": "downloaded",
        "type": "audio",
        "audio_path": str(audio_file),
        "audio_filename": audio_file.name,
        "audio_format": audio_format,
        "file_size": _format_filesize(file_size),
        "file_size_bytes": file_size,
        "output_dir": str(out_path),
        "metadata": _build_metadata_dict(meta, url),
    }

    _save_meta(result, out_path)
    return result


def cmd_playlist(
    url: str,
    output_dir: str = "~/Downloads",
    quality: str | None = None,
) -> dict:
    """Download all videos in a playlist."""
    err = _check_ytdlp()
    if err:
        return err

    out_path = Path(output_dir).expanduser()
    out_path.mkdir(parents=True, exist_ok=True)

    video_template = str(out_path / "%(playlist_index)03d - %(title).70s.%(ext)s")
    fmt = _get_format_string(quality)

    dl_cmd = [
        "yt-dlp",
        "-f", fmt,
        "--merge-output-format", "mp4",
        "-o", video_template,
        "--no-overwrites",
        "--yes-playlist",
        url,
    ]

    print("Downloading playlist...", file=sys.stderr)
    dl_result = subprocess.run(dl_cmd, capture_output=True, text=True, timeout=3600)

    if dl_result.returncode != 0 and not list(out_path.glob("*.mp4")):
        return {"error": f"Playlist download failed: {dl_result.stderr.strip()[:500]}"}

    # Collect all downloaded files
    video_files = sorted(out_path.glob("*.mp4"), key=lambda p: p.name)
    if not video_files:
        # Try other extensions
        for ext in [".mkv", ".webm", ".mov"]:
            video_files.extend(out_path.glob(f"*{ext}"))
        video_files.sort(key=lambda p: p.name)

    if not video_files:
        return {"error": f"Playlist download completed but no video files found in {out_path}"}

    items = []
    total_size = 0
    for vf in video_files:
        sz = vf.stat().st_size
        total_size += sz
        items.append({
            "video_path": str(vf),
            "video_filename": vf.name,
            "file_size": _format_filesize(sz),
            "file_size_bytes": sz,
        })

    result = {
        "status": "downloaded",
        "type": "playlist",
        "total_videos": len(items),
        "total_size": _format_filesize(total_size),
        "total_size_bytes": total_size,
        "output_dir": str(out_path),
        "videos": items,
    }

    _save_meta(result, out_path)
    return result


def cmd_formats(url: str) -> dict:
    """List all available formats for a URL."""
    err = _check_ytdlp()
    if err:
        return err

    result = subprocess.run(
        ["yt-dlp", "-F", "--no-playlist", url],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        return {"error": f"Failed to list formats: {result.stderr.strip()[:500]}"}

    lines = result.stdout.strip().splitlines()

    formats = []
    header_found = False
    for line in lines:
        if line.startswith("ID") or line.startswith("---"):
            header_found = True
            continue
        if not header_found:
            continue
        if not line.strip():
            continue

        parts = line.split()
        if len(parts) < 3:
            continue

        fmt = {
            "format_id": parts[0],
            "ext": parts[1] if len(parts) > 1 else "",
            "description": " ".join(parts[2:]) if len(parts) > 2 else "",
            "raw": line.strip(),
        }
        formats.append(fmt)

    # Also get metadata for context
    meta, _ = _get_metadata(url)
    title = meta.get("title", "Unknown") if meta else "Unknown"

    return {
        "title": title,
        "url": url,
        "total_formats": len(formats),
        "formats": formats,
    }


def cmd_info(url: str) -> dict:
    """Show video metadata without downloading."""
    err = _check_ytdlp()
    if err:
        return err

    print("Fetching info...", file=sys.stderr)
    meta, err = _get_metadata(url)
    if err:
        return err

    return {
        "title": meta.get("title", "Unknown"),
        "uploader": meta.get("uploader", "Unknown"),
        "uploader_url": meta.get("uploader_url", ""),
        "upload_date": meta.get("upload_date", ""),
        "duration_seconds": meta.get("duration", 0),
        "duration": _timestamp_str(meta.get("duration", 0)),
        "view_count": meta.get("view_count"),
        "like_count": meta.get("like_count"),
        "comment_count": meta.get("comment_count"),
        "description": (meta.get("description") or "")[:1000],
        "webpage_url": meta.get("webpage_url", url),
        "resolution": f"{meta.get('width', '?')}x{meta.get('height', '?')}",
        "fps": meta.get("fps"),
        "vcodec": meta.get("vcodec", ""),
        "acodec": meta.get("acodec", ""),
        "filesize_approx": _format_filesize(meta.get("filesize_approx")),
        "thumbnail": meta.get("thumbnail", ""),
        "categories": meta.get("categories", []),
        "tags": (meta.get("tags") or [])[:20],
        "subtitles_available": bool(meta.get("subtitles") or meta.get("automatic_captions")),
    }


# ─── CLI ────────────────────────────────────────────────────────────────────────


def main():
    parser = argparse.ArgumentParser(
        description="Video Downloader — Download videos, audio, and playlists from any URL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s download "https://youtube.com/watch?v=dQw4w9WgXcQ"
  %(prog)s download "https://youtube.com/watch?v=..." --quality 720 --output-dir ~/Videos
  %(prog)s audio "https://youtube.com/watch?v=..." --audio-format m4a
  %(prog)s playlist "https://youtube.com/playlist?list=..."
  %(prog)s formats "https://youtube.com/watch?v=..."
  %(prog)s info "https://youtube.com/watch?v=..."
        """,
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # download
    dl_p = sub.add_parser("download", help="Download single video")
    dl_p.add_argument("url", help="Video URL")
    dl_p.add_argument("--output-dir", default="~/Downloads", help="Output directory (default: ~/Downloads)")
    dl_p.add_argument("--quality", default=None, help="Max quality: 360, 480, 720, 1080, 4k (default: 1080)")
    dl_p.add_argument("--format", dest="format_id", default=None, help="Specific format ID (from 'formats' output)")
    dl_p.add_argument("--no-subs", action="store_true", help="Skip subtitle download")

    # audio
    au_p = sub.add_parser("audio", help="Download audio only")
    au_p.add_argument("url", help="Video URL")
    au_p.add_argument("--output-dir", default="~/Downloads", help="Output directory (default: ~/Downloads)")
    au_p.add_argument("--audio-format", default="mp3", choices=["mp3", "m4a", "opus"], help="Audio format (default: mp3)")

    # playlist
    pl_p = sub.add_parser("playlist", help="Download all videos in a playlist")
    pl_p.add_argument("url", help="Playlist URL")
    pl_p.add_argument("--output-dir", default="~/Downloads", help="Output directory (default: ~/Downloads)")
    pl_p.add_argument("--quality", default=None, help="Max quality: 360, 480, 720, 1080, 4k (default: 1080)")

    # formats
    fmt_p = sub.add_parser("formats", help="List available formats/qualities")
    fmt_p.add_argument("url", help="Video URL")

    # info
    info_p = sub.add_parser("info", help="Show video metadata without downloading")
    info_p.add_argument("url", help="Video URL")

    args = parser.parse_args()

    if args.command == "download":
        result = cmd_download(args.url, args.output_dir, args.quality, args.format_id, not args.no_subs)
        print(json.dumps(result, indent=2))
        if "error" not in result:
            print(f"\nDownloaded to {result['video_path']}", file=sys.stderr)
            print(f"Size: {result['file_size']}", file=sys.stderr)

    elif args.command == "audio":
        result = cmd_audio(args.url, args.output_dir, args.audio_format)
        print(json.dumps(result, indent=2))
        if "error" not in result:
            print(f"\nDownloaded audio to {result['audio_path']}", file=sys.stderr)
            print(f"Size: {result['file_size']}", file=sys.stderr)

    elif args.command == "playlist":
        result = cmd_playlist(args.url, args.output_dir, args.quality)
        print(json.dumps(result, indent=2))
        if "error" not in result:
            print(f"\nDownloaded {result['total_videos']} videos to {result['output_dir']}", file=sys.stderr)
            print(f"Total size: {result['total_size']}", file=sys.stderr)

    elif args.command == "formats":
        result = cmd_formats(args.url)
        print(json.dumps(result, indent=2))
        if "error" not in result:
            print(f"\n{result['total_formats']} formats available for: {result['title']}", file=sys.stderr)

    elif args.command == "info":
        result = cmd_info(args.url)
        print(json.dumps(result, indent=2))
        if "error" not in result:
            print(f"\n{result['title']} ({result['duration']})", file=sys.stderr)

    if "error" in result:
        sys.exit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Video Automation — YouTube & TikTok
Usage:
  python main.py run                          # Start daily scheduler
  python main.py generate                     # Generate one video now
  python main.py generate --niche tech        # Specific niche
  python main.py generate --platform tiktok   # Specific platform
  python main.py setup --platform youtube     # OAuth setup wizard
  python main.py setup --platform tiktok      # TikTok setup wizard
  python main.py status                       # Print stats
  python main.py niches                       # List available niches
"""

import argparse
import logging
import os
import sys
import json
from pathlib import Path


def _configure_logging(level: str = "INFO"):
    try:
        import colorlog
        handler = colorlog.StreamHandler()
        handler.setFormatter(
            colorlog.ColoredFormatter(
                "%(log_color)s%(asctime)s [%(levelname)s]%(reset)s %(name)s — %(message)s",
                datefmt="%H:%M:%S",
                log_colors={
                    "DEBUG": "cyan",
                    "INFO": "green",
                    "WARNING": "yellow",
                    "ERROR": "red",
                    "CRITICAL": "bold_red",
                },
            )
        )
    except ImportError:
        handler = logging.StreamHandler()
        handler.setFormatter(
            logging.Formatter("%(asctime)s [%(levelname)s] %(name)s — %(message)s", datefmt="%H:%M:%S")
        )

    root = logging.getLogger()
    root.setLevel(getattr(logging, level.upper(), logging.INFO))
    root.handlers.clear()
    root.addHandler(handler)


def _load_config():
    from config import Config
    return Config()


# ── Commands ─────────────────────────────────────────────────────────────────

def cmd_run(args):
    """Start the daily scheduler."""
    config = _load_config()
    _configure_logging(config.LOG_LEVEL)

    errors = config.validate()
    if errors:
        print("\n[ERROR] Missing required configuration:")
        for e in errors:
            print(f"  • {e}")
        print("\nEdit your .env file and re-run. See .env.example for reference.")
        sys.exit(1)

    from src.scheduler.runner import DailyScheduler
    scheduler = DailyScheduler(config)
    scheduler.start()


def cmd_generate(args):
    """Generate a single video immediately."""
    config = _load_config()
    _configure_logging(config.LOG_LEVEL)

    if not config.ANTHROPIC_API_KEY:
        print("[ERROR] ANTHROPIC_API_KEY not set in .env")
        sys.exit(1)

    from src.niches.manager import NicheManager
    from src.content.collector import DataCollector
    from src.content.generator import ContentGenerator
    from src.video.creator import VideoCreator
    from src.database.manager import DatabaseManager
    from src.upload.youtube import YouTubeUploader
    from src.upload.tiktok import TikTokUploader

    niche_mgr = NicheManager()
    platform = args.platform or "youtube"

    if args.niche:
        niche = niche_mgr.get(args.niche)
        if not niche:
            print(f"[ERROR] Unknown niche '{args.niche}'. Available: {niche_mgr.names()}")
            sys.exit(1)
    else:
        niches = niche_mgr.for_platform(platform)
        import random
        niche = random.choice(niches)
        print(f"Auto-selected niche: {niche.name}")

    print(f"\n{'='*50}")
    print(f"  Niche:    {niche.display_name}")
    print(f"  Platform: {platform}")
    print(f"{'='*50}\n")

    # Pipeline
    collector = DataCollector(config)
    generator = ContentGenerator(config)
    creator = VideoCreator(config)
    db = DatabaseManager()

    print("[1/4] Collecting trending data …")
    data = collector.collect(niche)
    print(f"      Found {len(data['topics'])} topics, {len(data['facts'])} facts")

    print("[2/4] Generating script with AI …")
    script = generator.generate(data, niche, platform)
    print(f"      Title: {script['title']}")

    print("[3/4] Creating video …")
    video_path = creator.create_video(script, niche.name, platform)
    if not video_path:
        print("[ERROR] Video creation failed")
        sys.exit(1)
    print(f"      Saved: {video_path}")

    video_id = db.save_video(
        niche=niche.name,
        platform=platform,
        title=script.get("title", ""),
        description=script.get("description", ""),
        tags=script.get("tags", []),
        file_path=video_path,
    )

    print("[4/4] Uploading …")
    if platform == "youtube" and config.UPLOAD_TO_YOUTUBE:
        try:
            uploader = YouTubeUploader(config)
            result = uploader.upload(video_path, script, niche)
            db.save_upload(video_id, "youtube", result["platform_id"], result["url"], "success")
            print(f"      YouTube: {result['url']}")
        except Exception as exc:
            print(f"      YouTube upload failed: {exc}")
    elif platform == "tiktok" and config.UPLOAD_TO_TIKTOK:
        try:
            uploader = TikTokUploader(config)
            result = uploader.upload(video_path, script, niche)
            db.save_upload(video_id, "tiktok", result["platform_id"], result["url"], "success")
            print(f"      TikTok: {result['url']}")
        except Exception as exc:
            print(f"      TikTok upload failed: {exc}")
    else:
        print("      Upload disabled or credentials not configured — video saved locally only.")

    print(f"\n✓ Done! Video at: {video_path}")


def cmd_setup(args):
    """Run setup wizard for a platform."""
    platform = args.platform or "youtube"
    if platform == "youtube":
        from src.upload.youtube import YouTubeUploader
        YouTubeUploader.setup_wizard()
    elif platform == "tiktok":
        from src.upload.tiktok import TikTokUploader
        TikTokUploader.setup_wizard()
    else:
        print(f"Unknown platform: {platform}")


def cmd_status(args):
    """Print statistics."""
    _configure_logging("WARNING")
    from src.database.manager import DatabaseManager
    db = DatabaseManager()
    stats = db.get_stats()
    print(f"\n{'='*40}")
    print("  Video Automation — Status")
    print(f"{'='*40}")
    print(f"  Total videos generated : {stats['total_videos']}")
    print(f"  Videos today           : {stats['today']}")
    print(f"  Successful uploads     : {stats['successful_uploads']}")
    if stats["by_niche"]:
        print("\n  By niche:")
        for niche, count in sorted(stats["by_niche"].items(), key=lambda x: -x[1]):
            print(f"    {niche:<15} {count}")
    print()


def cmd_niches(args):
    """List all available niches."""
    from src.niches.manager import NicheManager
    mgr = NicheManager()
    print(f"\n{'='*50}")
    print("  Available Niches")
    print(f"{'='*50}")
    for n in mgr.get_all():
        platforms = ", ".join(n.platforms)
        print(f"  {n.name:<14} — {n.display_name:<25} [{platforms}]")
    print()


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        prog="python main.py",
        description="YouTube & TikTok Video Automation",
    )
    sub = parser.add_subparsers(dest="command")

    sub.add_parser("run", help="Start the daily scheduler")

    gen_p = sub.add_parser("generate", help="Generate one video now")
    gen_p.add_argument("--niche", help="Niche name (see: niches command)")
    gen_p.add_argument("--platform", choices=["youtube", "tiktok"], default="youtube")

    setup_p = sub.add_parser("setup", help="Authentication setup wizard")
    setup_p.add_argument("--platform", choices=["youtube", "tiktok"], required=True)

    sub.add_parser("status", help="Show statistics")
    sub.add_parser("niches", help="List available niches")

    args = parser.parse_args()

    dispatch = {
        "run": cmd_run,
        "generate": cmd_generate,
        "setup": cmd_setup,
        "status": cmd_status,
        "niches": cmd_niches,
    }

    if args.command in dispatch:
        dispatch[args.command](args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()

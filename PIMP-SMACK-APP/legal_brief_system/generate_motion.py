#!/usr/bin/env python3
"""Render Ninth Circuit motion blocks into a single document."""

import argparse
import json
import shutil
from datetime import datetime
from pathlib import Path
from typing import Dict, List

try:
    from jinja2 import Environment, BaseLoader, StrictUndefined
except ImportError as exc:
    raise SystemExit(
        "jinja2 is required. Activate the venv and run 'pip install jinja2'."
    ) from exc

BASE_DIR = Path(__file__).resolve().parent
DEFAULT_MOTIONS_DIR = BASE_DIR / "motions"
DEFAULT_BLOCKS_DIR = BASE_DIR / "templates" / "motion_blocks"
DEFAULT_OUTBOX_DIR = BASE_DIR.parent / "OUTBOX"


def load_json(path: Path) -> Dict:
    with path.open("r", encoding="utf-8") as fh:
        return json.load(fh)


def render_block(template_text: str, context: Dict) -> str:
    env = Environment(
        loader=BaseLoader(),
        autoescape=False,
        trim_blocks=True,
        lstrip_blocks=True,
        undefined=StrictUndefined,
    )
    template = env.from_string(template_text)
    return template.render(**context).strip()


def render_motion(block_sequence: List[str], blocks_dir: Path, context: Dict) -> str:
    rendered_sections: List[str] = []
    for block_id in block_sequence:
        block_path = blocks_dir / f"{block_id}.md"
        if not block_path.exists():
            raise FileNotFoundError(f"Missing block template: {block_path}")
        block_text = block_path.read_text(encoding="utf-8")
        section = render_block(block_text, context)
        if section:
            rendered_sections.append(section)
    return "\n\n".join(rendered_sections).strip()


def write_output(text: str, motion_dir: Path, motion_key: str, case_number: str,
                 motion_title: str, outbox_dir: Path) -> Dict[str, Path]:
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_case = case_number.replace(" ", "")
    safe_title = motion_title.replace(" ", "_").replace("'", "")
    filename = f"{safe_case}-{motion_key}-{timestamp}.md"

    outputs_dir = motion_dir / "outputs"
    outputs_dir.mkdir(parents=True, exist_ok=True)
    output_path = outputs_dir / filename
    output_path.write_text(text, encoding="utf-8")

    outbox_dir.mkdir(parents=True, exist_ok=True)
    outbox_motion = outbox_dir / "motions"
    outbox_motion.mkdir(exist_ok=True)
    outbox_chrono = outbox_dir / "chronological"
    outbox_chrono.mkdir(exist_ok=True)

    motion_copy = outbox_motion / filename
    chrono_copy = outbox_chrono / filename
    shutil.copy2(output_path, motion_copy)
    shutil.copy2(output_path, chrono_copy)

    return {
        "local": output_path,
        "outbox_motion": motion_copy,
        "outbox_chronological": chrono_copy,
        "timestamp": timestamp,
    }


def append_log(outbox_dir: Path, record: Dict) -> None:
    log_path = outbox_dir / "chronological" / "motion-log.json"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    if log_path.exists():
        data = json.loads(log_path.read_text(encoding="utf-8"))
    else:
        data = []
    data.append(record)
    log_path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a motion from block templates")
    parser.add_argument("--motion-key", help="Name of the motion folder under motions/", required=False)
    parser.add_argument("--config", help="Path to a motion config JSON", required=False)
    parser.add_argument("--motions-dir", default=str(DEFAULT_MOTIONS_DIR), help="Base motions directory")
    parser.add_argument("--blocks-dir", default=str(DEFAULT_BLOCKS_DIR), help="Directory containing block templates")
    parser.add_argument("--outbox-dir", default=str(DEFAULT_OUTBOX_DIR), help="OUTBOX directory root")
    args = parser.parse_args()

    motions_dir = Path(args.motions_dir)
    blocks_dir = Path(args.blocks_dir)
    outbox_dir = Path(args.outbox_dir)

    if args.config:
        config_path = Path(args.config)
    elif args.motion_key:
        config_path = motions_dir / args.motion_key / "inputs" / "config.json"
    else:
        parser.error("Provide --motion-key or --config")

    if not config_path.exists():
        raise FileNotFoundError(f"Config not found: {config_path}")

    config = load_json(config_path)
    block_sequence = config.get("block_sequence")
    if not block_sequence:
        raise ValueError("Motion config missing 'block_sequence'")

    motion_dir = config_path.parent.parent
    rendered_text = render_motion(block_sequence, blocks_dir, config)

    paths = write_output(
        rendered_text,
        motion_dir,
        config.get("motion_key", args.motion_key or config_path.parent.name),
        config.get("case_number", ""),
        config.get("motion_title", "MOTION"),
        outbox_dir,
    )

    append_log(
        outbox_dir,
        {
            "motion_key": config.get("motion_key"),
            "motion_title": config.get("motion_title"),
            "case_number": config.get("case_number"),
            "timestamp": paths["timestamp"],
            "files": {
                "local": str(paths["local"]),
                "outbox_motion": str(paths["outbox_motion"]),
                "outbox_chronological": str(paths["outbox_chronological"]),
            },
        },
    )

    print("============================================================")
    print("MOTION GENERATED")
    print("============================================================")
    print(f"Local file:        {paths['local']}")
    print(f"OUTBOX (motions):  {paths['outbox_motion']}")
    print(f"OUTBOX (chrono):   {paths['outbox_chronological']}")
    print("============================================================")


if __name__ == "__main__":
    main()

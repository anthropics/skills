#!/usr/bin/env python3
"""voice-prompt listener.

Records mic audio in chunks, transcribes locally with faster-whisper, types
the result into the focused window, and presses Enter on a trigger phrase.

Features
--------
- Cross-platform typing (macOS osascript / Linux xdotool / Windows pyautogui).
- Pause/resume via voice: "pause listening" / "resume listening".
- Self-learning vocabulary: every accepted prompt (text before a submit
  trigger) is appended to ~/.claude/skills/voice-prompt/state/history.txt and
  used as Whisper's `initial_prompt` so it learns the words *you* actually use
  (function names, library names, jargon, your accent's habits).
- Learner can be toggled at runtime: "stop learning" / "start learning".
- A user-editable vocabulary file at state/vocab.txt is always prepended.
"""

from __future__ import annotations

import argparse
import platform
import queue
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

import numpy as np
import sounddevice as sd
from faster_whisper import WhisperModel

# ---------- config ------------------------------------------------------------

SAMPLE_RATE = 16000
CHUNK_SECONDS = 2.5
MODEL_SIZE = "base.en"
COMPUTE_TYPE = "int8"
SILENCE_RMS = 0.005

TRIGGER_WORDS = {
    "go", "send", "send it", "enter", "hit enter",
    "submit", "submit it", "do it",
}
STOP_WORDS = {"stop listening", "quit listening", "exit voice", "stop voice"}
PAUSE_WORDS = {"pause listening", "pause voice", "mute", "mute voice", "go to sleep"}
RESUME_WORDS = {"resume listening", "resume voice", "unmute", "unmute voice", "wake up"}
LEARN_OFF_WORDS = {"stop learning", "pause learning", "no more learning", "stop training"}
LEARN_ON_WORDS = {"start learning", "begin learning", "resume learning", "start training"}

STATE_DIR = Path.home() / ".claude" / "skills" / "voice-prompt" / "state"
VOCAB_FILE = STATE_DIR / "vocab.txt"      # user-editable, one term/phrase per line
HISTORY_FILE = STATE_DIR / "history.txt"  # auto-appended accepted prompts
FLAG_FILE = STATE_DIR / "learn.enabled"   # persists learner on/off between runs
HISTORY_MAX_LINES = 500
INITIAL_PROMPT_MAX_CHARS = 900            # Whisper caps around ~224 tokens

SYSTEM = platform.system()


# ---------- typing backends ---------------------------------------------------

def _mac_run(script: str) -> None:
    subprocess.run(["osascript", "-e", script], check=False,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def _type_mac(text: str) -> None:
    safe = text.replace("\\", "\\\\").replace('"', '\\"')
    _mac_run(f'tell application "System Events" to keystroke "{safe}"')


def _enter_mac() -> None:
    _mac_run('tell application "System Events" to key code 36')


def _type_linux(text: str) -> None:
    subprocess.run(["xdotool", "type", "--delay", "1", "--", text], check=False)


def _enter_linux() -> None:
    subprocess.run(["xdotool", "key", "Return"], check=False)


def _type_win(text: str) -> None:
    import pyautogui
    pyautogui.write(text, interval=0.005)


def _enter_win() -> None:
    import pyautogui
    pyautogui.press("enter")


def pick_backend():
    if SYSTEM == "Darwin":
        return _type_mac, _enter_mac, "AppleScript (osascript)"
    if SYSTEM == "Linux":
        if not shutil.which("xdotool"):
            sys.exit("ERROR: xdotool not found. Install with: sudo apt install xdotool")
        return _type_linux, _enter_linux, "xdotool"
    if SYSTEM == "Windows":
        try:
            import pyautogui  # noqa: F401
        except ImportError:
            sys.exit("ERROR: pyautogui missing. Run: pip install pyautogui")
        return _type_win, _enter_win, "pyautogui"
    sys.exit(f"ERROR: unsupported platform: {SYSTEM}")


type_text, press_enter, BACKEND_NAME = pick_backend()


# ---------- vocab / learner ---------------------------------------------------

def ensure_state() -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    if not VOCAB_FILE.exists():
        VOCAB_FILE.write_text(
            "# voice-prompt vocab — one term or short phrase per line.\n"
            "# Add words / names / jargon you use a lot so Whisper learns them.\n"
            "# Lines starting with # are ignored.\n"
        )
    if not HISTORY_FILE.exists():
        HISTORY_FILE.write_text("")


def learner_enabled() -> bool:
    # File present (any content) ⇒ on. Default: on.
    return not (FLAG_FILE.exists() and FLAG_FILE.read_text().strip() == "off")


def set_learner(on: bool) -> None:
    FLAG_FILE.write_text("on" if on else "off")


def load_vocab_lines() -> list[str]:
    if not VOCAB_FILE.exists():
        return []
    out = []
    for line in VOCAB_FILE.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            out.append(line)
    return out


def load_history_lines() -> list[str]:
    if not HISTORY_FILE.exists():
        return []
    return [l for l in HISTORY_FILE.read_text().splitlines() if l.strip()]


def build_initial_prompt() -> str | None:
    """Combine user vocab + recent accepted prompts to bias Whisper."""
    parts: list[str] = []
    parts.extend(load_vocab_lines())
    if learner_enabled():
        parts.extend(load_history_lines()[-80:])
    if not parts:
        return None
    prompt = " ".join(parts)
    if len(prompt) > INITIAL_PROMPT_MAX_CHARS:
        prompt = prompt[-INITIAL_PROMPT_MAX_CHARS:]
    return prompt


def append_history(text: str) -> None:
    if not learner_enabled():
        return
    text = text.strip()
    if not text:
        return
    with HISTORY_FILE.open("a") as f:
        f.write(text + "\n")
    lines = HISTORY_FILE.read_text().splitlines()
    if len(lines) > HISTORY_MAX_LINES:
        HISTORY_FILE.write_text("\n".join(lines[-HISTORY_MAX_LINES:]) + "\n")


# ---------- matching helpers --------------------------------------------------

def normalize(s: str) -> str:
    return s.lower().strip().rstrip(".!?, ")


def matches_any(text: str, phrases: set[str]) -> str | None:
    norm = normalize(text)
    for p in sorted(phrases, key=len, reverse=True):
        if p in norm:
            return p
    return None


def ends_with_trigger(text: str) -> tuple[bool, str, str]:
    norm = normalize(text)
    for trig in sorted(TRIGGER_WORDS, key=len, reverse=True):
        if norm == trig:
            return True, trig, ""
        if norm.endswith(" " + trig):
            return True, trig, text[: -len(trig)].rstrip(".!?, ")
    return False, "", text


# ---------- audio loop --------------------------------------------------------

def recorder(audio_q: "queue.Queue[np.ndarray]", stop: threading.Event) -> None:
    block = int(SAMPLE_RATE * CHUNK_SECONDS)
    with sd.InputStream(samplerate=SAMPLE_RATE, channels=1, dtype="float32") as stream:
        while not stop.is_set():
            buf, _ = stream.read(block)
            audio_q.put(buf[:, 0].copy())


def main() -> int:
    parser = argparse.ArgumentParser(description="voice-prompt listener")
    parser.add_argument("--no-learn", action="store_true",
                        help="start with the learner OFF for this session")
    parser.add_argument("--model", default=MODEL_SIZE,
                        help=f"whisper model size (default: {MODEL_SIZE})")
    args = parser.parse_args()

    ensure_state()
    if args.no_learn:
        set_learner(False)

    print(f"voice-prompt: platform={SYSTEM}  backend={BACKEND_NAME}")
    print(f"voice-prompt: loading faster-whisper model={args.model} compute={COMPUTE_TYPE}")
    print("  (first run downloads ~150MB, then it's cached)")
    sys.stdout.flush()
    model = WhisperModel(args.model, device="cpu", compute_type=COMPUTE_TYPE)

    print(f"  learner    : {'ON' if learner_enabled() else 'OFF'} "
          f"(vocab={len(load_vocab_lines())} terms, "
          f"history={len(load_history_lines())} prompts)")
    print(f"  vocab file : {VOCAB_FILE}")
    print(f"  triggers   : {sorted(TRIGGER_WORDS)}")
    print(f"  pause/res  : {sorted(PAUSE_WORDS)} ↔ {sorted(RESUME_WORDS)}")
    print(f"  learn off  : {sorted(LEARN_OFF_WORDS)}")
    print(f"  learn on   : {sorted(LEARN_ON_WORDS)}")
    print(f"  exit       : {sorted(STOP_WORDS)}")
    print("Switch focus to your Claude Code window now. Listening starts in 3s…")
    sys.stdout.flush()
    time.sleep(3)
    print("[listening]")
    sys.stdout.flush()

    audio_q: "queue.Queue[np.ndarray]" = queue.Queue()
    stop = threading.Event()
    threading.Thread(target=recorder, args=(audio_q, stop), daemon=True).start()

    muted = False
    initial_prompt = build_initial_prompt()

    try:
        while True:
            audio = audio_q.get()
            if float(np.abs(audio).mean()) < SILENCE_RMS:
                continue
            segments, _ = model.transcribe(
                audio,
                language="en",
                vad_filter=True,
                vad_parameters=dict(min_silence_duration_ms=300),
                initial_prompt=initial_prompt,
            )
            text = " ".join(s.text.strip() for s in segments).strip()
            if not text:
                continue
            print(f"  heard{' (muted)' if muted else ''}: {text}")
            sys.stdout.flush()

            # --- control commands run even when muted ----------------------
            if matches_any(text, STOP_WORDS):
                print("[stop word — exiting]")
                break
            if matches_any(text, PAUSE_WORDS):
                muted = True
                print("[paused — say 'resume listening' to continue]")
                sys.stdout.flush()
                continue
            if matches_any(text, RESUME_WORDS):
                muted = False
                print("[resumed]")
                sys.stdout.flush()
                continue
            if matches_any(text, LEARN_OFF_WORDS):
                set_learner(False)
                print("[learner OFF — accepted prompts will not be saved]")
                sys.stdout.flush()
                continue
            if matches_any(text, LEARN_ON_WORDS):
                set_learner(True)
                initial_prompt = build_initial_prompt()
                print("[learner ON — accepted prompts will be saved]")
                sys.stdout.flush()
                continue

            if muted:
                continue

            # --- normal dictation flow -------------------------------------
            matched, trig, remainder = ends_with_trigger(text)
            if matched:
                if remainder:
                    type_text(remainder + " ")
                    time.sleep(0.15)
                    append_history(remainder)
                    initial_prompt = build_initial_prompt()
                press_enter()
                print(f"  → submitted (trigger: '{trig}')"
                      f"{'  [learned]' if learner_enabled() and remainder else ''}")
                sys.stdout.flush()
            else:
                type_text(text + " ")
    except KeyboardInterrupt:
        print("\n[interrupted]")
    finally:
        stop.set()
    return 0


if __name__ == "__main__":
    sys.exit(main())

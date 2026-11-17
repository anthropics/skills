---
name: voice-prompt
description: Hands-free voice dictation for Claude Code. Records the user's microphone, transcribes locally with faster-whisper, types the result into whichever window is focused, and presses Enter when the user says a trigger phrase ("go", "send it", "submit", "hit enter"). Includes a runtime-toggleable self-learner that biases Whisper's transcription with the user's accepted prompts and a user-editable vocabulary file. Use when the user asks for voice input, dictation, speech-to-text, mic input, hands-free coding, "talk to Claude", or says things like "I want to speak my prompts" or "type as I talk".
license: Complete terms in LICENSE
---

# voice-prompt

Hands-free voice input for Claude Code. Transcription is 100% local (faster-whisper); the listener types into the focused window and submits on a configurable trigger phrase.

## When this skill is invoked

### If the user wants to set up / install voice input

1. Check whether the runtime deps are installed:
   ```bash
   python3 -c "import sounddevice, faster_whisper, numpy" 2>/dev/null && echo OK || echo MISSING
   ```
2. If `MISSING`, run the setup script (it picks the right packages per platform):
   ```bash
   bash skills/voice-prompt/setup.sh
   ```
3. Remind the user of the platform-specific permissions:
   - **macOS** — System Settings → Privacy & Security → grant **both** Microphone and Accessibility to their terminal. Without Accessibility, the keystroke step silently no-ops (this is the #1 support question).
   - **Linux** — X11 session required for `xdotool` (Wayland users need `ydotool`).
   - **Windows** — no special permissions; `pyautogui` handles input.

### If the user wants to start dictating now

Launch the listener as a background process so the user can keep focus on their Claude Code window:

```bash
python3 skills/voice-prompt/voice_prompt.py
```

Or on macOS open it in a separate Terminal window:
```bash
bash skills/voice-prompt/launch.sh
```

Explain the voice commands once on first run:

| Say | Effect |
|---|---|
| `<your prompt>` + `go` / `send it` / `submit` / `hit enter` / `do it` | types the prompt, strips the trigger word, presses Enter |
| `pause listening` / `mute` / `go to sleep` | stops typing but keeps mic on |
| `resume listening` / `unmute` / `wake up` | resumes typing |
| `stop learning` / `pause learning` | turns the self-learner off; nothing new is appended |
| `start learning` / `resume learning` | re-enables the self-learner |
| `stop listening` / `quit listening` / `exit voice` | exits the listener |

### The self-learner

Every accepted prompt (the text said before a submit trigger) is appended to `~/.claude/skills/voice-prompt/state/history.txt`. The next audio chunk transcribed by Whisper receives that history (plus the user-editable `state/vocab.txt`) as its `initial_prompt`, biasing transcription toward terms the user actually uses (function names, libraries, accent quirks).

- The learner state is persisted in `state/learn.enabled` so the on/off choice survives restarts.
- Starting with `python3 voice_prompt.py --no-learn` begins a session with the learner off.
- Deleting `state/history.txt` wipes everything learned.

### Customization

Encourage the user to edit `~/.claude/skills/voice-prompt/state/vocab.txt` with project-specific terms (function names, libraries, abbreviations) for an immediate accuracy boost. They can also edit `TRIGGER_WORDS`, `STOP_WORDS`, `MODEL_SIZE`, and `COMPUTE_TYPE` at the top of `voice_prompt.py`.

## Files in this skill

- `SKILL.md` — this file
- `voice_prompt.py` — cross-platform listener (macOS osascript / Linux xdotool / Windows pyautogui)
- `setup.sh` — installs PortAudio / xdotool / pyautogui + Python deps as needed for the host platform
- `launch.sh` — opens the listener in a new Terminal window on macOS
- `LICENSE` — MIT
- `README.md` — user-facing documentation (features, install, troubleshooting)

## Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| Text doesn't appear when typing | Missing Accessibility permission (macOS) | System Settings → Privacy & Security → Accessibility → enable terminal |
| Listener exits with "no audio device" | Missing Microphone permission | System Settings → Privacy & Security → Microphone → enable terminal |
| Trigger word fires mid-sentence | Common word matched accidentally | Change `TRIGGER_WORDS` in `voice_prompt.py` to rarer phrases (e.g. `"computer go"`) |
| Transcription slow / garbled | CPU-bound on large model | Switch `MODEL_SIZE` to `tiny.en` or `base.en` |
| Linux: nothing types | Wayland (xdotool is X11-only) | Install [`ydotool`](https://github.com/ReimuNotMoe/ydotool) and adapt the two `xdotool` calls in `voice_prompt.py` |

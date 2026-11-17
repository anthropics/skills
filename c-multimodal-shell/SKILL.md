---
name: c-multimodal-shell
description: Build or extend C-only, English-configured, stateless multimodal model shells that ingest XML training manifests for vision/audio/text placeholders, expose 40 numbered training slots plus a level-41 Markdown slot, avoid vector embeddings, and include local GGUF computer-control console hooks for screenshots, mouse position, button coordinates, grid overlays, streaming ticks, mouse/keyboard execution, and response-safe overlays.
---

# C Multimodal Shell

## Core Rules

- Use C for runnable code and English for prompts, labels, comments, XML tags, and Markdown notes.
- Do not introduce Python, JavaScript, TypeScript, Rust, Go, or other runtime languages into generated shells.
- Keep training stateless by default: each command loads only the current XML/Markdown inputs and does not persist learned memory unless the user explicitly asks for part-two memory work.
- Do not add vector embeddings. Represent training material as indexed slot records, source paths, modality labels, and plain text metadata.
- Treat the first 40 levels as XML-backed slots and level 41 as the Markdown expansion slot.

## Starting Point

Copy `assets/c-shell-template/` into the target project when the user wants a working scaffold. The template contains:

- `main.c`: C99 command shell, XML slot manifest loader, slot-40 dictionary lookup, level-41 Markdown loader, console state model, one-second tick loop, and stubbed GGUF/screen-control adapters.
- `Makefile`: C-only build commands.
- `training_slots.xml`: example 40-slot XML manifest with slot 40 reserved for `dictionary.xml`.
- `dictionary.xml`: grounded word dictionary where each word may have multiple definitions.
- `level_41.md`: example Markdown slot.
- `shakti_memory_schema.xml`: post-41 permanent internal memory/control schema.
- `tool_menu_config.xml`: four-section tiered tool menu for MCP-controlled tool discovery.
- `history_log_example.xml`: append-only XML history shape keyed by epoch time.

Compile with `make`, then run `./c_multimodal_shell --xml training_slots.xml --md level_41.md --ticks 3`.

## Build Workflow

1. Create or update the C scaffold from `assets/c-shell-template/`.
2. Keep external integrations behind C function boundaries:
   - `capture_screen_frame` for screenshots and temporary grid overlay capture.
   - `detect_buttons` for button labels and coordinates.
   - `stream_model_tick` for GGUF streaming updates.
   - `operate_mouse_keyboard` for actual input execution.
3. Store detected controls as English labels plus coordinate placeholders such as `BTN_01`, `BTN_02`, and `MOUSE_CURRENT`.
4. Make the persistent tick non-destructive: if the model is responding, enqueue or display an overlay update rather than restarting generation.
5. Preserve the stateless baseline: every tick may inspect the current screen state, but the scaffold should not save training memory across runs until the user requests memory.

## Response Path

Explain this distinction when users ask why the scaffold does not answer yet:

- The template shell can load the 40 XML slots, load level 41 Markdown, build a frame packet, and format prompt-ready screen/button state.
- Shakti can route a response when the MCP gate sends an XML message packet into the C shell, the shell adds grounded slot data, and the local model runtime returns either an English reply or an action request.
- Slot 40 is the grounded dictionary slot. When Shakti hits an unknown or skipped word such as `the` or `as`, lookup the word in XML and return every matching definition.
- After level 41, load permanent internal memory from XML schemas keyed by epoch time.

For a first end-to-end demo, use `--prompt`, `--dict`, and `--lookup` to show the prompt packet and dictionary pull. For production, replace the dry-run GGUF adapter with the local C/C++ runtime that Tyler selects.

## XML Slot Shape

Use simple XML records so training files can be plugged in later:

```xml
<training>
  <slot id="1" modality="text" path="training/text_01.txt">English description.</slot>
  <slot id="2" modality="vision" path="training/image_01.png">English description.</slot>
  <slot id="3" modality="audio" path="training/audio_01.wav">English description.</slot>
</training>
```

Require slot ids 1 through 40 for the base manifest. Use level 41 only for Markdown instructions, declarations, or higher-level policy text.

## Computer-Control Console Requirements

When implementing the console feature:

- Capture a screenshot every second while control mode is active.
- Include current mouse x/y coordinates with each frame.
- Detect or ingest all visible buttons with x/y/w/h coordinates.
- Convert button coordinates to placeholders before passing them to the local GGUF model.
- Add a clear grid to the captured screenshot only for the model-facing image; do not leave the grid on the user’s live display.
- Stream model output so overlay updates can be injected while the model is mid-response.
- Execute mouse and keyboard actions only through explicit C adapter functions with a safety gate that can be reviewed or replaced per operating system.

## Post-41 Memory and MCP Gate

Use `shakti_memory_schema.xml` as the permanent internal memory/control schema after level 41. The MCP is the middleman for CPU access, heartbeat, internet, shell, tools, message storage, history search, and mouse/keyboard approval. Keep history append-only and move reflected task records to XML keyed by epoch time.

Use `tool_menu_config.xml` to keep tool prompts small. Show Shakti only four high-level tool sections first, then let her request details by category. Include TI-83 calculation, approved directory/file access, screen ticks, gated mouse/keyboard action requests, URL fetch, and web search as MCP-routed tools.

Use the chat window spec in `shakti_memory_schema.xml`: dark C/C++ UI, log/approved-directory tab, chat tab, heartbeat switch, timer toggle, tool cutoff, and max 9 auto responses before shutoff unless Tyler changes controls.

## References

Read `references/control-console-contract.md` when adding OS-specific screenshot, overlay, mouse, keyboard, or GGUF integrations.

Read `references/making-the-model-respond.md` when the user asks what is needed beyond training data, why the scaffold does not generate real model text yet, or how to connect prompts to a local GGUF runtime.

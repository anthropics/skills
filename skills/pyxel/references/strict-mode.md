# Strict Mode

Use for requested release checks, audits, or proof bundles. Extend the verification workflow in [SKILL.md](../SKILL.md) with coverage of the game's relevant paths and retained evidence; ordinary edits do not require this mode.

## Coverage

- Exercise reachable success, failure, retry, and rejected actions when the game defines them. Choose concrete cases from its rules: a puzzle may need a solvable route and an illegal move; an action game may need collision consequences and recovery.
- Check representative scenes directly, including transitions and HUD changes affected by the work. Use a recording or multiple frames when timing matters; use `diff_frames` when a pixel comparison answers a specific question.
- Render the sound or music targets under review and verify that the intended runtime events trigger them. Distinguish successful rendering from a listening judgment.
- Use `read_palette`, `read_image`, or `read_tilemap` when their facts help diagnose an asset issue.

Resolve observed defects and rerun affected checks before declaring readiness. Report uncovered paths or unavailable checks as limitations; successful tool calls alone do not establish that the game meets the request.

## Evidence

When evidence must be retained, use the project's existing location or an agreed output directory. Save only what supports the review:

- representative frames with explicit `output` paths rather than disposable inline files;
- recordings or WAV files for motion or audio checks that required them;
- controls, reproduction commands, observed results, and limitations in the requested report or existing review record.

Create a separate report file or machine-readable bundle only when requested or needed by downstream work.

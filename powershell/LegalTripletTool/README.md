# LegalTripletTool (PowerShell)

PowerShell module for legal-evidence extraction workflows:
- ingest XML/JSON/PDF references,
- flatten JSON/XML into subject-predicate-object triplets,
- preserve selected object blocks as atomic JSON (no destructive splitting),
- resolve `Fact.id` ↔ `arg_id` and `seed_arg_id` relationships,
- run exact/fuzzy/backoff phrase search,
- merge near-duplicate objects into branches,
- export a unified machine-consumable output,
- prototype a local GGUF-driven computer-control capture loop.

## Install from terminal

From this repository root:

```powershell
pwsh -NoProfile -Command "Import-Module ./powershell/LegalTripletTool/LegalTripletTool.psd1 -Force"
```

Optional persistent install:

```powershell
pwsh -NoProfile -Command "\
  $dest = Join-Path $HOME 'Documents/PowerShell/Modules/LegalTripletTool'; \
  New-Item -ItemType Directory -Path $dest -Force | Out-Null; \
  Copy-Item ./powershell/LegalTripletTool/* $dest -Recurse -Force; \
  Import-Module LegalTripletTool -Force"
```

## Quick start

```powershell
$collection = Get-LegalObjectCollection -Path ./evidence -Recurse -AttemptPdfText -NoSplitProperties Triplet,Temporal,Meta
$triplets = $collection | ConvertTo-LegalTripletSet -IncludeLinks
$matches = Search-LegalTriplets -Triplets $triplets -Query "failure to disclose" -Mode Backoff -MaxMatches 50
$seedLinks = Resolve-LegalSeedLinks -Collection $collection
$unified = Merge-LegalObjectsUnifiedOutput -Collection $collection -BranchSimilarity 0.90 -AskBeforeRemoval
Export-LegalUnifiedOutput -UnifiedOutput $unified -Path ./out/unified.json
```

## Handling your XML Fact IDs + JSON arg IDs

Use `Resolve-LegalSeedLinks` to map:
- XML `Fact id="F001"` style items,
- JSON `arg_id` direct matches (e.g., `F017`),
- JSON `seed_arg_id` chain matches (e.g., `ECF60F015/F017`).

This gives you a cross-file map that can be used as your chain/domino relationship graph.

## Search modes

- `Exact`: literal string search across `Subject + Predicate + Object`.
- `Fuzzy`: Levenshtein-based whole-record similarity (`-MinimumSimilarity`).
- `Backoff`: starts with full query, then shorter prefixes until hits are found.

## Linking behavior for large content

Large documents are represented as links instead of being inlined (`LinkThresholdChars`).
This preserves source fidelity and avoids destructive rewriting of content.

## Computer control console prototype

`Start-ComputerControlConsole` captures:
- screenshot with temporary grid overlay,
- mouse coordinates,
- optional button map loaded from JSON,
- button placeholders (`BTN_1`, `BTN_2`, ...),
- 1-second ticks by default.

Streaming mode (`-EnableStreaming`) keeps response context as an overlay payload for the next tick.
Optional `-EnableInputControl` allows model-returned action JSON to drive mouse and keyboard.

Example action JSON expected from model response:

```json
{
  "actions": [
    {"type": "mousemove", "x": 640, "y": 380},
    {"type": "click", "x": 640, "y": 380},
    {"type": "sendkeys", "keys": "^l"}
  ]
}
```

# LegalTripletTool (PowerShell)

PowerShell module for legal-evidence extraction workflows:
- ingest XML/JSON/PDF references,
- flatten JSON/XML into subject-predicate-object triplets,
- preserve selected object blocks as atomic JSON (no destructive splitting),
- resolve `Fact.id` ↔ `arg_id` and `seed_arg_id` relationships,
- run exact/fuzzy/backoff phrase search,
- build Stage-1 source-normalized XML + checkpoint file for citation-target tracing,
- prototype a local GGUF-driven computer-control capture loop.

## Install from terminal

```powershell
pwsh -NoProfile -Command "Import-Module ./powershell/LegalTripletTool/LegalTripletTool.psd1 -Force"
```

## Stage 1 (source XML normalization + checkpoint)

`Build-EvidenceSourceXml` is the first controlled stage for your pipeline.

What it does:
- requires a source XML input (ex: `ECF60_fact_id_triplet_source.xml`),
- outputs a normalized XML in working root with `_source` removed from filename,
- normalizes dates to `YYYY-MM-DD` where parsable,
- normalizes fact IDs to `[Court_Docketing_No]_[fact_id]` (not hardcoded),
- adds `<Action>` from `<Event>` (keeps existing data, avoids breaking compatibility),
- extracts citation targets (`ECF##`, `ECF##-##`, `Document ##`, `ER ##`) from statement/citation text,
- creates a checkpoint JSON showing required targets and whether matching files were found,
- can create immutable snapshot copies of originals in `working_root/original_snapshots`.

Example:

```powershell
$result = Build-EvidenceSourceXml `
  -SourceXmlPath ./input/ECF60_fact_id_triplet_source.xml `
  -WorkingRoot ./work `
  -EvidenceFilesRoot ./evidence `
  -CreateSnapshot

$result
Get-Content -Raw $result.CheckpointPath | ConvertFrom-Json
```

## Existing commands

```powershell
$collection = Get-LegalObjectCollection -Path ./evidence -Recurse -AttemptPdfText -NoSplitProperties Triplet,Temporal,Meta
$triplets = $collection | ConvertTo-LegalTripletSet -IncludeLinks
$matches = Search-LegalTriplets -Triplets $triplets -Query "failure to disclose" -Mode Backoff -MaxMatches 50
$seedLinks = Resolve-LegalSeedLinks -Collection $collection
```

## Computer control console prototype

`Start-ComputerControlConsole` captures:
- screenshot with temporary grid overlay,
- mouse coordinates,
- optional button map loaded from JSON,
- button placeholders (`BTN_1`, `BTN_2`, ...),
- 1-second ticks by default.

Streaming mode (`-EnableStreaming`) keeps response context as an overlay payload for the next tick.
Optional `-EnableInputControl` allows model-returned action JSON to drive mouse and keyboard.

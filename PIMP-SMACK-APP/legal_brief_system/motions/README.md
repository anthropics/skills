# Motion Workspace

Each motion gets its own folder under `legal_brief_system/motions/<motion_key>/` with the following structure:

```
<motion_key>/
  inputs/        # JSON config + any data snippets used for rendering
  attachments/   # Supporting exhibits referenced in the motion
  outputs/       # Generated DOCX/PDF copies (also mirrored to OUTBOX)
```

Keep configs in `inputs/config.json` so the generator can load them automatically. The legacy `legal_brief_system/data/motion_*.json` files now just point here.

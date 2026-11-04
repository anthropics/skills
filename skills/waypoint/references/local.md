# Local paths and dependencies

## Establish the boundary

Use exact absolute paths. Inspect links without automatically following them; identify filesystem, volume, file type, permissions, and sync-provider involvement. A streamed/mirrored Drive item follows the Drive workflow unless provider identity/behavior is verified. Local files may have no cloud ID; never invent one.

Distinguish renaming a symlink from moving its target. Relative symlinks can break on relocation. Finder aliases, application bookmarks, Windows shortcuts, and hard links behave differently; inspect the applicable type instead of assuming links track every move.

## Preflight

- Detect occupied destinations, including dangling symlinks and case/Unicode-normalized collisions where relevant. Use no-replacement execution semantics, not merely a prior existence check.
- Reject duplicate targets, cycles, unknown sources, folder merges, and unrequested type changes. Plan batches as a whole.
- Handle case-only renames, swaps, and parent/child paths explicitly. Temporary names must be unique, same-volume, bounded, and in the reverse map; do not improvise collision workarounds.
- Keep extensions unless explicitly requested. An extension change is not format conversion.
- Check known dependencies: files being written, open applications, repositories/worktrees, imports, config, scripts, shortcuts, and document-relative links. Search authorized project roots with `rg`/`rg --files`. Report scope; do not scan all user data by default.
- Do not move OS folders, app-managed Codex/Claude state, repository internals, or sync-provider roots as routine cleanup. Use the owning application's supported migration route.

## Same-volume operations

Prefer a native same-volume rename/move that refuses destination replacement. Discover a suitable platform API/tool; do not assume `mv` or a high-level move helper preserves identity or refuses overwrite. Capture filesystem identity and suitable content evidence before execution. Verify identity/content at the destination and absence at the old path. Preserve bytes, directory contents, permissions, and extended metadata; ctime may legitimately change. Inodes/file IDs are volume-specific evidence, not permanent global identifiers.

Use structured arguments so spaces, apostrophes, leading dashes, newlines, dollar signs, and backticks stay path data. Recheck drift before execution. Never take ownership or disable protections as a workaround for denied access.

## Cross-volume migration

Cross-volume moves typically copy and remove the source; the original filesystem identity cannot survive. Do not silently use this fallback. Explain and proceed only with authorization for those migration semantics, including source removal.

For an authorized migration, inventory content/metadata, copy without replacement, verify hashes where appropriate plus structure/metadata and critical references, then remove only verified original items within scope. Keep originals on failure; equal names/sizes are not sufficient integrity proof. Avoid persistent duplicate masters and report precisely which copies remain if completion is blocked.

## References and rollback

Paths change even when filesystem identity survives. Repair references only within authorized scope and run relevant application/build/link checks. Do not silently add compatibility aliases/symlinks. Pause a move with a known essential consumer that cannot be repaired within scope.

Record old/new paths, identity/content evidence, authorized reference repairs, and reverse map. Undo needs fresh no-overwrite/dependency checks. After uncertain success inspect both paths/identities before retrying. Never blanket-delete “duplicates” or claim every reference works without evidence.

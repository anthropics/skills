# Drive identity and moves

## Resolve and inspect

Read source and destination metadata by verified Drive ID: name, MIME type, parents, drive/owner, trash state, capabilities, shortcut target, and modification/version information where available. Inspect sharing/inherited access sufficiently to assess a move. A successful metadata read does not establish every collaborator's access.

Resolve names through authorized search in the correct account and parent. Ask if several candidates remain. Distinguish a shortcut's own ID from its target ID; operate on the requested object. For folders, check destination ancestry to prevent cycles. Follow pagination when completeness matters; a truncated listing is not a complete inventory or collision check.

Check collisions even though Drive allows duplicate names. Never merge/replace same-named objects or substitute a shortcut to make an unsupported move appear successful.

## Update the existing object

- Rename: `files.update` on the existing `fileId`, changing only `name`.
- Move: `files.update` on that same ID, with `addParents` set to the verified destination ID and `removeParents` restricted to the verified source parents being removed. Preserve unrelated parent relationships supported by the provider.
- Rename and move may share one supported metadata update. Leave upload/content-byte and MIME-conversion fields unset. No create, copy, export, import, upload, or trash action belongs in this operation.
- Move a folder by changing its parent, without recreating children. Child Drive IDs must remain unchanged.
- Use current Shared Drive capabilities and restrictions. If a connector lacks a required option, report the gap; use another already-authorized API route if available, never object recreation.

## Access and references

A parent change may change inherited access. Same-ID does not mean same-access. Review cross-drive, ownership, account, public/shared-folder, and business-context boundaries before executing. Do not broaden permissions as a workaround. If a potential disclosure or required-access loss cannot be assessed, pause that move and state the exact gap; an independently authorized safe rename may proceed.

Check known name/path consumers in authorized scope: scripts searching filenames, folder-path configuration, manifests, sync clients, integrations, and application location rules. Preserve ID-based URLs and resource keys. Do not rewrite every link or search unrelated private material unnecessarily.

## Verification and recovery

Reread the original ID after mutation. Compare requested name/parents, MIME type, shortcut target, available checksum/content evidence, and relevant access state. Metadata updates may legitimately change modification/version fields; that alone is not evidence of changed content. For folder changes, retain a child-ID manifest appropriate to scope and distinguish full checks from samples.

After a timeout, fetch the original ID: desired state means do not repeat; unchanged state may allow a bounded retry; unexpected state means reconcile. If identity/content invariants fail, stop dependents. Never delete an unexpected object to “recover”.

Reverse mapping includes ID, old/new names, original/new parents, access evidence, timestamp, and result. Reversal requires checking that the old parent exists, user edits have not intervened, and access remains appropriate.

Primary references: [files.update](https://developers.google.com/workspace/drive/api/reference/rest/v3/files/update), [folder moves](https://developers.google.com/workspace/drive/api/guides/folder). Consult current official documentation for changing restrictions.

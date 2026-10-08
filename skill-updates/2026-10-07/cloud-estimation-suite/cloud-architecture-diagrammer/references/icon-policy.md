# Icon selection and provenance

Use labelled provider-neutral symbols by default. Names of providers and
services may label generic shapes; never generate an imitation proprietary
logo. This skill's CC BY licence covers methodology, not provider artwork.
The locally supplied common icon policy and renderer are authoritative for
supported formats, source allowlists and validation limits.

When official provider artwork is requested, obtain it directly from the
provider's official architecture icon pack and inspect the current terms.
Record provider, official source URL, applicable licence/redistribution and
trademark conditions, capture date and whether the intended export and
public redistribution are permitted. A source URL or checksum alone does
not establish provider authorship or permission. If terms are unclear,
use neutral symbols and retain the unresolved rights decision.

The canonical renderer accepts a local pack containing `manifest.json`:

- Required manifest fields: `provider`, `official_source_url`, `assets`.
- At least one nonempty rights notice: `licence`, `license` or
  `trademark_notice`.
- Every asset: safe pack-relative `path` and `sha256`; only PNG is supported.
- No unlisted assets, path traversal, duplicate files, invalid images or
  mismatched hashes. Match each node's provider to its chosen asset.

Do not bundle downloaded SVG logos directly: they are unsupported by this
renderer. If permitted conversion is needed, preserve original provenance
and terms, and hash the local converted PNG. A complete, locally verified
pack is still a declaration from its supplier; retain the acquisition and
rights evidence in sources.

Missing, corrupt, unsupported or incompletely documented packs fall back
to labelled neutral symbols. Preserve renderer warnings, never silently
claim official icons were used. Provenance for used icons includes relative
path, SHA-256, provider, official URL and licence/trademark notice. Keep
these notices with SVG/PNG exports and in the workbook manifest; do not leak
local filesystem paths into public artifacts. Follow any additional rights
notice requirements outside the image itself.

Provider assets are optional runtime inputs. Do not commit proprietary logo
files to the public source or package them in `.skill` bundles unless the
applicable permission has been established. A synthetic neutral test image
may exercise provenance mechanics, but cannot prove official pack rights.

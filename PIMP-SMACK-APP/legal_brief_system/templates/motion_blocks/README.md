# Motion Block Library

Each file in this folder is a single reusable building block written in Jinja2 syntax. The generator picks a `block_sequence` array (see `MOTION_SHELL.md`) and concatenates the rendered blocks in that order. Blocks never write custom prose; they only insert data from the JSON sources.

## Available Blocks

| File | Purpose | Inputs |
| --- | --- | --- |
| `00_cover.md` | Optional cover sheet for motions that need one | `cover_fields.*` |
| `10_caption.md` | Standard caption + title | `court_name`, `case_number`, `case_title`, `motion_title` |
| `20_introduction.md` | Relief summary paragraph(s) | `moving_party`, `relief_requested[]`, `emergency_basis` |
| `30_factual_background.md` | Narrative facts | `motion_facts[]` with cites |
| `32_jurisdiction.md` | Jurisdiction/authority statements | `jurisdiction_blocks[]` |
| `40_legal_standard.md` | Multiprong tests or rule recitals | `legal_standard.heading`, `legal_standard.points[]`, `supporting_citations[]` |
| `50_argument_section.md` | Single argument heading + body | `arguments[]` items |
| `60_relief.md` | Closing relief paragraph + signature | `moving_party`, `relief_requested[]`, `signature_block` |
| `70_attachments.md` | Exhibit list | `attachments[]` |
| `80_certificate_compliance.md` | Word-count statement | `word_count` |
| `90_certificate_service.md` | Service list | `service_date`, `service_list[]` |

Add new blocks as needed (e.g., declarations, factual appendices) and reference them from the block sequence.

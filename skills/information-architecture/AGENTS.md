# Repository Guidelines

## Project Structure & Module Organization
- `SKILL.md` captures the skill definition, usage guidance, and book outline; edit carefully to keep terminology accurate.
- `references/Information_Architecture_-_Louis_Rosenfeld.md` is the full text reference; avoid wholesale rewrites and keep searches anchored to this file; figures live in `references/assets/`.
- Aside from the extracted figures, no compiled artifacts are expected; keep contributions text-first.

## Build, Test, and Development Commands
- No build pipeline is required; changes are plain text/Markdown.
- Use `rg -n "<term>" references/Information_Architecture_-_Louis_Rosenfeld.md` to locate supporting excerpts quickly.
- Run `wc -w AGENTS.md SKILL.md` to keep contributions concise and within intended length.

## Coding Style & Naming Conventions
- Write in concise, instructional Markdown with clear headings; prefer short paragraphs and bullet lists over long prose.
- Maintain consistent book and chapter titles exactly as in the source text; avoid ad-hoc abbreviations.
- When adding commands, use fenced code blocks with shell info strings (```bash```) and keep examples runnable from the repo root.
- Filenames should remain ASCII, descriptive, and kebab- or snake-case; avoid spaces.

## Testing Guidelines
- Manual validation only: proofread for accuracy against the reference text and ensure links/paths match the repo layout.
- If adding search examples, test them locally (e.g., `rg -i -n "navigation systems" references/Information_Architecture_-_Louis_Rosenfeld.md`) to confirm they return results.
- Keep documents between roughly 200–400 words unless a specific brief requires otherwise.

## Commit & Pull Request Guidelines
- Follow the existing history pattern: concise, capitalized summaries with optional issue/PR references (e.g., `Update skill overview (#12)`).
- In PRs, include: purpose of the change, summary of sections touched (`SKILL.md`, reference snippets, new docs), and any verification steps run.
- Screenshots are unnecessary; quote relevant lines instead when demonstrating reference usage or search outputs.

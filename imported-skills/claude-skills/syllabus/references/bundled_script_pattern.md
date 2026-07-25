# Bundled Script Pattern — Why JS for DOCX Generation, Not Inline

This reference answers exactly one decision: **why does the syllabus skill ship a bundled `generate_reading_list.js` script rather than inlining the DOCX generation logic in SKILL.md?**

## The Core Trade

DOCX generation requires ~300 lines of `docx`-package boilerplate (table layouts, hyperlink patterns, list formatting, page setup, etc.). This logic is:

1. **Reusable** across runs — every reading list uses the same DOCX layout
2. **Mechanical** — no LLM judgment required; just JSON-in / DOCX-out
3. **Long-lived** — the layout doesn't change between runs

Inlining 300 lines of mechanical layout code in SKILL.md means:
- The skill prompt is much longer (token cost on every invocation)
- Layout changes require editing the skill prompt (high-risk)
- The skill body has to re-derive the same logic each run

Bundling the logic in `scripts/generate_reading_list.js` means:
- The skill body is ~200 lines lighter (token-efficient)
- Layout changes are isolated to one file
- The skill orchestrates; the script executes mechanically

## When to Bundle (vs Inline)

### Bundle when:

- ✅ The logic is mechanical (no LLM judgment)
- ✅ The logic is reusable across runs (same layout / same algorithm)
- ✅ The logic is non-trivial (>50 lines)
- ✅ The logic is in a non-Python language (JS, Go, Rust, etc.)
- ✅ The logic has external dependencies (`docx` package, `requests`, etc.)

### Inline (in SKILL.md) when:

- The logic requires LLM judgment per run (e.g., paper-summary writing)
- The logic is short (<20 lines) and run-specific
- The logic is in-context-only (uses session-specific tool calls)
- The logic varies significantly per invocation

## The Pattern Used Here

`scripts/generate_reading_list.js`:

1. **Accepts JSON input + output path as CLI args**
   ```bash
   node generate_reading_list.js --input data.json --output result.docx
   ```

2. **Has a documented JSON schema** (in SKILL.md so the orchestrator knows what to produce)

3. **Handles `docx` require with multi-location fallback** (works whether `docx` is installed locally, globally, or in a parent dir)

4. **Validates input** (missing fields → graceful error, not silent failure)

5. **Produces a clean professional DOCX** with:
   - Title page
   - Introduction (with Consensus link)
   - Learning outcomes box
   - Numbered papers per section
   - Footer with metadata

6. **Uses canonical `docx` patterns**:
   - `ExternalHyperlink` with full URLs
   - `LevelFormat.BULLET` for lists
   - Dual-width tables (`columnWidths` + cell `width`)

## Skill Orchestrator's Role

The skill body (SKILL.md):

1. Walks Phase 0 intake
2. Parses syllabus + extracts topics
3. Walks group-and-confirm checkpoint
4. Runs Consensus searches (LLM judgment per query)
5. Writes summaries + discussion questions (LLM judgment per paper)
6. **Constructs the JSON payload** matching the bundled script's schema
7. **Invokes the script** with the JSON
8. Validates output + delivers

The skill body is responsible for **what goes in the document**. The script is responsible for **how it's laid out**.

## Why Node.js Specifically

The `docx` library is a JavaScript library (npm package). Could the skill use a Python `docx` library (`python-docx`)? Yes, but:

- The repo's other research-pack DOCX-generating skills (litreview, grants, dossier) all use Node.js + `docx`
- Consistency: one DOCX library across the research pack
- The `docx` JS library is more actively maintained + has richer features
- `python-docx` doesn't support all the features the skill needs (advanced hyperlinks, table styling)

## File Structure

```
research/syllabus/skills/syllabus/scripts/
├── citation_tracker.py            ← stdlib Python (orchestration helper)
├── topic_grouper.py               ← stdlib Python (orchestration helper)
├── discussion_question_validator.py ← stdlib Python (orchestration helper)
└── generate_reading_list.js       ← BUNDLED Node.js (mechanical DOCX assembly)
```

The Python scripts are stateless helpers (per-run). The JS script is the bundled mechanical assembler (called once per run).

## Anti-Patterns

### "Inline the JS into a Python script via subprocess"

Adds an unnecessary layer. The skill should call `node` directly.

### "Convert JS logic to Python to keep all scripts in one language"

Loses access to the better-maintained `docx` JS library. Worse: would diverge from sibling skills (litreview, grants, dossier all use `docx` JS).

### "Keep the JS script but inline the JSON schema in the script"

The JSON schema needs to be IN SKILL.md so the orchestrator knows what to construct. Documenting it in the script alone hides it from the orchestrator's prompt context.

### "Inline 300 lines of docx code in SKILL.md"

The original anti-pattern. Bloats the prompt, makes layout changes risky, makes the skill body harder to read.

### "Import the script from another skill"

Cross-skill dependencies break the per-skill self-contained discipline (per CLAUDE.md anti-patterns). Even though it would save duplication, the bundled script lives within syllabus's own folder.

## Operational Checklist

- [ ] `scripts/generate_reading_list.js` exists in syllabus's scripts/ folder
- [ ] Script accepts `--input <json>` + `--output <docx>` CLI args
- [ ] Script handles `docx` require with multi-location fallback
- [ ] Script validates input (missing fields → graceful error)
- [ ] JSON schema documented in SKILL.md (not just in the script)
- [ ] Skill orchestrator constructs JSON matching the schema
- [ ] Skill orchestrator invokes the script via `node` (not `python`)
- [ ] DOCX output validated post-generation

## Citations (7 sources)

1. **Karpathy-coder discipline + write-a-skill conventions** (this repo's `engineering/write-a-skill/`). Source for the "stdlib-only Python tools, bundled non-Python scripts allowed for mechanical jobs" pattern.

2. **CLAUDE.md anti-pattern: "Don't add features beyond what the task requires."** The bundled script honors this — it does ONE thing (DOCX layout) and does it mechanically.

3. **`docx` Node.js package — github.com/dolanmiu/docx (MIT).** Authoritative source for the API patterns the bundled script uses. Active maintenance, comprehensive feature set.

4. **CommonJS / Node.js module resolution algorithm.** Source for the "multi-location fallback" pattern in the require statement. Ensures the script works in development (local node_modules) and production (global install).

5. **Twelve-Factor App principles — III. Config: store config in the environment.** Source for the CLI-args-not-config pattern. Script accepts input/output as args, not via env vars or config files.

6. **Brian Kernighan & P. J. Plauger, *Software Tools* (1976).** Source for the "do one thing well + compose" pattern. The bundled script does exactly one thing (mechanical DOCX assembly); the skill body composes it with the rest of the pipeline.

7. **Doug McIlroy / Unix philosophy.** Source for the broader pattern: "Write programs that do one thing and do it well. Write programs to work together. Write programs to handle text streams, because that is a universal interface." JSON-in / DOCX-out is the modern equivalent.

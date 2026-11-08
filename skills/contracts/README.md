# Contract Reasoning

> See **Security** below before running on real contracts.

Answers questions across a corpus of contract documents with verified citations. You ask in plain English — "which of these contracts let the buyer terminate for convenience, and on what notice?" — and the session you're talking to turns that into a research brief, shows you a plan, and waits for your go. Then it reads every contract in parallel, tool-less extraction passes (reader agents rescue whatever those can't finish), filing cited findings into a local SQLite database, and composes the answer in chat from those findings. Every claim carries a quote that was verified against the source document when it was recorded.

The engine is a **local MCP server that ships with the plugin** (`servers/documents/src/index.mjs`) — it runs on your machine, owns the database and document extraction, and makes no network calls of its own. All reads and writes flow through its typed tools. (One caveat worth knowing up front: liteparse's OCR downloads a tesseract language file on first use — see Prerequisites.)

**Run this locally, not in a remote container.** Document parsing is heavy, deliberately local work, and its cache lives on disk. Remote environments (Claude Cowork's cloud sessions, containerized runners) work against both halves of that: their filesystems are wiped between sessions, so every session re-parses the whole corpus from scratch, and their small CPU allocations make OCR of scanned documents take hours instead of minutes. On your own machine the corpus parses once, is cached by content, and every later question starts instantly.

## Prerequisites

- **Node.js ≥ 22.13** on your PATH (the server checks at startup and says so plainly if it's missing or too old). The server runs with no install at all; installing liteparse (below) is only needed for scans and Office formats.
- **[liteparse](https://www.npmjs.com/package/@llamaindex/liteparse)** — `cd <plugin>/servers/documents && npm install`. **Required for scanned PDFs, and for DOCX/XLSX/PPTX at all.** It is the only extractor here that can OCR: on a scanned page `pdftotext -layout` returns nothing (measured: 0 characters), so without liteparse that contract is filed unreadable and drops out of every answer. A corpus of text-layer PDFs works without it. The server finds it at `$LITEPARSE_PATH`, in its own `node_modules`, or as `lit` on PATH, and reports which one in `extractor`.

  (The server's `.npmrc` pins the public npm registry, so the install behaves the same whether or not your global npm config points somewhere else.)

  **OCR is not offline.** The first OCR run downloads a tesseract language file (`eng.traineddata`, ~15 MB) and caches it (`~/Library/Application Support/tesseract-rs/tessdata/` on macOS). On an airgapped host, pre-stage that file and set `TESSDATA_PREFIX`, or extraction of scans will fail with no obvious cause. Text-layer extraction (`lit parse --no-ocr`) needs no network.

## Quick start

**In Claude Code**, install the healthcare plugin:

```
/plugin marketplace add anthropics/healthcare
/plugin install healthcare@healthcare   # plugin-name @ marketplace-name
```

(If you received a tarball or repo path from us, point at that folder instead: `/plugin marketplace add /absolute/path/to/folder-containing-.claude-plugin`.)

**In your terminal**, set up a corpus in whatever project directory you want to work from:

```bash
mkdir -p corpora/mycontracts
cp your-contracts/* corpora/mycontracts/   # .pdf, .docx, .xlsx, .pptx, .txt, .md, .html
```

**Back in Claude Code**, started from that same directory:

```
/contracts which of these have an evergreen renewal clause?
```

The skill reads your contracts in on first use, then shows you a plan — how it read the question, what it will read — and waits for your go. That is the only pause. After you confirm, the reading happens silently and the answer arrives in chat: judgment calls, then the answer with a quote behind every claim. After the answer it asks how it was — that feedback (de-identified) goes into an observations log you can share with us.

## What's local

This is **single-user, local-only** today:

- State (db, observations log) lives at `~/.claude/data/healthcare/documents/` — machine-global so learned knowledge carries across projects, persists across plugin upgrades. Override the parent dir with `$CLAUDE_HEALTHCARE_DATA` (the server appends `/documents`). The server creates and writes this itself — no sandbox allowlisting needed.
- If a plugin upgrade changes the schema, the server says so on startup and names the file to delete: `~/.claude/data/healthcare/documents/data.sqlite` (the `parsed/` cache can stay). The corpus re-ingests automatically on the next `/contracts` — there's no migration.
- The contracts must be on the **local filesystem** — the same machine as the server. MCP connectors and other data-access patterns are planned.

## Choosing an extraction model

The reading passes accept a model override (`--model` on the sweep). We measure every candidate on two adversarial corpora: **paraphrase recall** (facts written as "carrying charge" instead of "late fee", defined-term indirection, negation traps — what a keyword reader misses) and **amendment-chain resolution** (does the answer assert a superseded term as current). Same rubric, same corpora, verified answer keys:

| extraction model | paraphrase recall | chain resolution (family mode) | 500-doc sweep* | docs needing rescue |
|---|---|---|---|---|
| opus | **100%** | 91% | 389s | **0.2%** |
| fable | 98% | **93%** | 463s | 0.2% |
| sonnet | 84% | 87% | 565s | 9% — reader agents recover the paraphrase gap (96% measured) at ~4× wall-clock |
| haiku | 72% | 88% | 590s | 26% — not recommended: quote rejections trigger retries, and recall misses are invisible to the rescue pass |

\*One machine (18-core laptop), concurrency 32, same 500-document corpus and rubric for every row — the relative shape is the signal, not the absolute seconds. Note the inversion: the "fast" model is the slowest sweep, because weak extraction pays for itself in retry rounds and rescue work.

Two lessons the table encodes: **chain resolution is architecture, not model** — grouping a family into one extraction call lifts every model's chain-resolution rate to ~87–93% and its stale-term trap rate to 0–8%, where per-document reading resolves only 53–64% of chains and asserts a displaced base term in 80–98% of the families that have one (both measured) — and **paraphrase recall is capability** — small models read past disguised vocabulary, and no downstream pass can recover what was never extracted. Default to the strongest model you have for extraction; the citations gate is identical regardless (a quote that isn't in the document is refused, whatever wrote it).

## Security

Contract text is untrusted input. The design keeps the blast radius structural, not behavioral:

- **Paths enter the system in one module** (`servers/documents/src/ingest.mjs`) and only through the two tools that take a directory — `corpus_register` and `corpus_prepare`. Both canonicalize it (symlinks resolved) and require a real directory; every other tool takes names and ids, and internal paths are derived from the corpora table. A quote inside a document can't steer any tool at a filesystem path.
- **The primary sweep holds no tools at all.** Each document is read by a one-shot extraction session spawned with every tool disabled (`--disallowed-tools "*"`) — it can emit findings and nothing else, and a quote that isn't verbatim in the document is refused at insert. Reader agents run only for the rescue pass and on surfaces without a `claude` CLI.
- **Reader agents get an enumerated tool allowlist, not a wildcard.** They process the untrusted text, so `documents-reader-mcp` is granted exactly five engine tools — `find` and `coverage` (its only writes) plus `doc_search`/`doc_text`/`shard_prompt` for the no-shared-disk path. No `sql`, no `write`, no `drop`, and neither of the two tools that accept a directory. (Until recently this was a `…__*` wildcard that granted all of them; a worker that reads attacker-supplied text should never have held `drop`.) This promise holds only when the plugin's own reader agents spawn — the sweep instructions now refuse to substitute a general agent if the readers are missing, because a substituted agent carries none of these restrictions.
- **A folder can define agents; never run inside one you didn't make.** On current Claude Code, a folder's `.claude/agents/` definitions can claim agent names — including this plugin's — and an agent definition can carry hooks that execute commands. That is a Claude Code-level issue (reported and being addressed there), and no plugin-side setting fully closes it. Until it is closed: never run Claude Code from inside, or `--add-dir`, a folder you received from outside. The documented flow is already the safe one — copy the files, not the folder, into a `corpora/` directory inside your own project (`cp received/*.pdf corpora/deal/` — a recursive folder copy would carry a hidden `.claude/` along); plain files carry no agent definitions, and subfolders aren't scanned for them.
- **The CLI worker is the weaker path, and knowingly so.** `documents-reader-cli` needs a shell to reach the engine, so it gets `Bash(node:*)` — scoped, so a `curl` or `rm` in a poisoned contract is refused, and no ToolSearch, so it cannot go find another server. But `node -e` can run anything: this raises the cost of an injection, it does not contain one. Prefer the MCP path when you have it, and see the last bullet.
- **The server makes no outbound network connections itself**, and runs without installing anything (liteparse is an exactly-pinned dependency with a committed lockfile, installed only when you need it). Extraction shells out to `lit`/`pdftotext`, which are local — with one exception: liteparse's **OCR** path fetches a ~15 MB tesseract language file (`eng.traineddata`) from a CDN the first time it runs, caching it under `~/Library/Application Support/tesseract-rs/tessdata/` (or the platform equivalent). `--no-ocr` extraction is network-free. Pre-stage that file on an airgapped host; don't assume the extraction step is offline just because the server is.
- Exact citations verify against `documents.content` at insert time via schema triggers — a fabricated verbatim quote structurally cannot exist, and citations are immutable after insert. The narrow exception is `judged` citations (non-contiguous evidence like table cells): those are model-attested with a recorded audit reference rather than substring-verified; `citations.kind` records which.
- **Don't run this on a corpus you don't trust.**

## Seeing the full run

The plan and the answer arrive in chat — the answer composed from verified findings, every fact backed by a quote that was substring-verified at insert. The whole run (findings, citations, judgment calls, learned facts) stays queryable in the database through the `sql` tool; nothing else is written.

## How it's built

- `SKILL.md` — the whole flow in one file, run by the session the user talks to: bootstrap, plan (with the one confirmation pause), scope, sweep, triage, and the chat answer. **This is the file to read or edit to understand or change run behavior.**
- `sweep.mjs` — the sweep: one toolless `claude -p` extraction per document (or per amendment family, via `--groups`, so supersession is resolved where the chain is visible), rows verified through the engine exactly like reader-written ones. Docs it can't finish fall to reader agents via the coverage gap check.
- `../../agents/documents-reader-mcp.md` — the reader agent: rescues the docs the direct sweep couldn't finish, and does the whole sweep on surfaces with no `claude` CLI. `documents-reader-cli.md` is the same role for the CLI transport (Bash instead of MCP tools, no ToolSearch). Readers are the only subagents in the design, spawned as plain typed Agent calls.
- `../../servers/documents/` — the server source (plain runnable `.mjs`, `node:sqlite`, no build step); `.mcp.json` runs `src/index.mjs` directly. `schema.sql` lives here — tables, views, triggers; citations verify against `documents.content` at insert time. Bare invocation speaks MCP over stdio; `src/index.mjs <tool> '<json>'` runs one tool call as a CLI, and `<tool> -` reads the JSON from stdin (heredoc — no shell escaping for document text). `citations.mjs` is the verification guarantee, `ingest.mjs` the text extraction, `engine.mjs` the run machinery.

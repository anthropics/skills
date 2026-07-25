# Memex Principles

Why the LLM Wiki pattern works, and why it failed for humans until LLMs.

## Vannevar Bush's Memex (1945)

In "As We May Think", Bush described a personal knowledge store where:

- Documents are curated, not just searched
- Users build **associative trails** — named, reusable paths through the material
- The trails are as valuable as the documents
- The system is private and personal, not a public reference

This is almost exactly the LLM Wiki pattern. The difference: Bush had no one to do the bookkeeping.

## Why humans abandon wikis

The value of a wiki grows linearly with its size. The maintenance burden grows faster. At some inflection point — usually around 50-100 pages — maintenance starts to feel like chores and the wiki goes stale.

Specific tasks that die first:

- Updating cross-references when a new page is added
- Keeping summary pages current
- Noticing when new data contradicts old claims
- Consolidating pages that have drifted apart
- Filing explorations back into the knowledge base
- Keeping the index current

Humans are great at reading, curating, and thinking about what things mean. They're bad at the bookkeeping. The bookkeeping is 80% of the work.

## What changed with LLMs

LLMs don't get bored. They don't forget to update a cross-reference. They can touch 15 files in one pass without losing track. They cost near-zero per maintenance operation.

This changes the economics. The wiki stays maintained because maintenance is now free (or nearly). The human's job collapses to:

- **Source curation** — deciding what's worth reading
- **Direction** — asking good questions, steering analysis
- **Judgment** — deciding when a contradiction matters
- **Taste** — knowing when the synthesis is wrong

Everything else — the 80% that killed human wikis — is delegated.

## Why not just RAG?

RAG retrieves fragments at query time and synthesizes from scratch every query. It works, but:

- **No accumulation.** Every subtle question re-derives the same synthesis.
- **Cross-references are computed on demand.** If the cross-reference needs 5 sources to be visible, you'd better hope all 5 are in the retrieval window.
- **Contradictions are invisible.** They surface only if you explicitly ask "is there a contradiction?"
- **Explorations disappear.** A comparison you worked out yesterday has to be re-derived tomorrow.

The wiki fixes all of these by **compiling the knowledge once**. The cross-references are already there. The contradictions have been flagged. The synthesis has absorbed everything read so far.

RAG is retrieve-then-think. The wiki is think-once-retrieve-many.

## When the wiki stops being enough

At ~500-1000 pages, the index approach starts to creak. Options:

1. **Layer on search.** Add `wiki_search.py` (BM25) or an external tool like [qmd](https://github.com/tobi/qmd) (hybrid BM25 + vector). Both work alongside the index.
2. **Shard by topic.** Split into multiple vaults by domain.
3. **Add an MCP retrieval layer.** Expose the wiki as a tool so agents can query it structurally.

The wiki and RAG are not opposites. The wiki is a **compiled layer above RAG**. You can run RAG on top of the wiki (indexing `wiki/`) and you'll get the benefits of both: pre-synthesized knowledge + scalable retrieval.

## The human role

A common failure mode: users delegate curation to the LLM ("just ingest all my Pocket articles"). Don't. Curation is where human judgment lives. The LLM can help you decide *whether* to read a source, but you pick what makes it into `raw/`.

If you let the LLM ingest everything, the wiki fills with low-signal summaries and the synthesis becomes meaningless. The wiki's value is a direct function of the quality of `raw/`.

## Reading recommendations

- Vannevar Bush, "As We May Think" (Atlantic, 1945)
- Andrej Karpathy's original LLM Wiki gist (linked from SKILL.md)
- Ousterhout's *A Philosophy of Software Design* — for why "deep modules" (well-summarized pages) beat shallow ones
- Niklas Luhmann's Zettelkasten — an earlier manual version of the same pattern

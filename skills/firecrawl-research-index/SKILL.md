---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-research-index
name: firecrawl-research-index
description: Find the papers that answer a research query in Firecrawl's research paper index — a corpus of paper abstracts whose largest share is biomedical and life-science literature (PubMed, bioRxiv, medRxiv), alongside arXiv preprints in CS, physics, and math — using semantic search, semantic and structural expansion, and in-body verification. Use this skill for literature-finding and paper-retrieval tasks of any kind, including clinical, biomedical, drug, gene, disease, and other life-science questions, whether the answer is a single paper or a full multi-paper set. The index is reached only through the `firecrawl_research_*` MCP tools or the `firecrawl research` CLI subcommands. Calling `firecrawl_search` with its `categories` option set to `["research"]` is a different feature — it filters ordinary web search to research-affiliated websites (the list includes PubMed, bioRxiv, medRxiv, arXiv, and publisher sites) and returns page results from them, without querying the paper records in this index.
---

# Firecrawl Research Index

Find the research papers that answer a research query. Some questions have a single answer; many have several — and when in doubt, lean toward returning the fuller relevant set (most relevant first) rather than narrowing to one. A reader is better served seeing the neighboring methods and papers than having them silently dropped.

## What is in the index

Paper abstracts, with full text reachable per paper. The largest share of the corpus is **biomedical and life-science** literature — **PubMed** journal articles plus **bioRxiv** and **medRxiv** preprints — so clinical, drug, gene, disease, epidemiology, and public-health questions are in scope. **arXiv** preprints cover computer science, physics, and mathematics. Coverage outside those sources is thinner: a paper that exists only behind a publisher paywall or in a niche venue may not be indexed, and the general web tools below are the fallback when it isn't.

There is **no fixed recipe**. Read the query, decide what kind it is, and choose the approach below. Some queries need a single search; others need heavy structural/semantic expansion. Don't run machinery a query doesn't call for.

## The tools, and what each is uniquely good at

- MCP: **`firecrawl_research_search_papers(query, k?)`**
  CLI: **`firecrawl research search-papers <query> [--k <number>]`**
  Semantic (HyDE) search over **abstracts**. The natural first move for almost any query.
  If results look thin or all-alike, re-run with a different framing (sibling domain, rival method, dataset/benchmark name) rather than giving up.

- MCP: **`firecrawl_research_related_papers(seed_ids, intent, mode?, k?)`**
  CLI: **`firecrawl research related-papers <seedIds...> --intent <intent> [--mode <similar|citers|references>] [--k <number>]`**
  Semantic and structural expansion, ranked to your `intent`.
  This reaches papers semantic search _cannot_, and it's how you turn one good hit into the rest of a set.
  `mode=similar` → niche siblings; `citers` → who uses/builds on the seeds; `references` → what they build on / compare against.

- MCP: **`firecrawl_research_inspect_paper(id)`**
  CLI: **`firecrawl research inspect-paper <id>`**
  Canonical metadata for **one** paper: title, abstract, authors, categories, source ids, and dates.
  Use it after `search_papers` or `related_papers` when you need the complete citation/metadata for a candidate, or when you have an id from elsewhere and need to confirm what paper it resolves to.
  This does **not** read the paper body; use `read_paper` for specific full-text questions.

- MCP: **`firecrawl_research_read_paper(id, question)`**
  CLI: **`firecrawl research read-paper <id> --question <question>`**
  In-body passages of **one** paper, to verify a load-bearing constraint (a method actually used, a score actually reported, an affiliation, what a paper compares to).
  Use it to settle a specific doubt, not on everything.

- MCP: **`firecrawl_search(query, categories: ["research"])`**
  CLI: **`firecrawl search <query> --categories research`**
  **Not this index.** This is a _website_ filter: it restricts a normal web search to a short list of research-affiliated domains — the list does include `pubmed.ncbi.nlm.nih.gov`, `biorxiv.org`, `medrxiv.org`, and `arxiv.org` alongside publisher sites — and returns page results in a `research` group beside `web`, each with `url`, `title`, `description` (the matched passage), `position`, and `category: "research"` — web results carry no `category`, so that is the field to key on when merging.
  So it reaches those sites' **web pages**; what it does not do is query their **paper records** in this index — no semantic search over abstracts, no citation-graph or related-paper expansion, no canonical paper metadata, and no in-body passages. The results are ordinary web results.
  Use it when you are **already** running a web search and want those sites weighed in the same call. For anything that is actually a paper-finding task, use `firecrawl_research_search_papers` and its siblings above.

- MCP: **`firecrawl_search(query)` / `firecrawl_scrape(url)`**
  CLI: **`firecrawl search <query>` / `firecrawl scrape <url>`**
  General **web** search and page fetch, for facts that don't live in paper abstracts: benchmark **leaderboards**, rankings, "who scores best / is largest / is most used."
  Find the ranking on the web, then map the top entries back to papers with `search_papers`.
  Reach for these only when the corpus can't answer the question on its own.

## Match the approach to the query

- **Single _named_ paper** ("the Qwen3 report") → one `search_papers`, done. This is the only case that truly wants exactly one paper.
- **Paper by description / by method or technique** ("the paper that introduced X", "training-free N-gram detection of AI text") → find the best match, then assume there's a _family_: expand with `related_papers` and **include the closely-related methods/papers too**. Even when one paper is the exact literal match, surface and keep its neighbors — don't narrow to the single best hit and reason the rest out. Only treat it as one-answer if the query names a specific paper.
- **Enumeration / method-family** ("papers that do X", "alternatives to Adam", "benchmarks for Y") → the answer is a _set_, and this is where `related_papers` earns its keep: expand several strong anchors with `mode=similar`, re-seed from new strong hits. One search is never enough here.
- **Exhibiting** ("papers that _use_ / exhibit property P") → the relevant papers apply P but their abstracts may not describe it. Go from P's defining paper outward via `citers`/`references`, and use `read_paper` to confirm a candidate actually uses P.
- **Superlative / leaderboard** ("best on benchmark X", "largest", "most popular") → the ranking lives on **leaderboards / the web**, not in any single abstract. Use `firecrawl_search` / `firecrawl_scrape` to find the benchmark's leaderboard or rankings, read off the top models/papers, then `search_papers` each to get its paper. As a fallback, search the benchmark and `read_paper` candidates for reported numbers. The hardest kind — cast wide.
- **Org / author filtered** ("from \<org\>", "by \<author\>") → topical match isn't enough; verify the affiliation/authorship (metadata or `read_paper`) before keeping a paper.
- **Compare-against** ("what does paper X benchmark against / build on") → the answer is _inside_ paper X: `read_paper(X, ...)` or `related_papers([X], ..., mode="references")`.

## Principles

- **Two different features share the word "research."** The paper index is `firecrawl_research_*` / `firecrawl research`. The `categories: ["research"]` option on `firecrawl_search` is a website filter — it does point web search at PubMed, bioRxiv, medRxiv, arXiv, and publisher sites, but what comes back is their web pages, not paper records. If a task is about finding papers, the tools in this skill are the ones that read the corpus; reaching for `categories: ["research"]` will quietly answer a different question.
- **Query shape and subject field are separate.** A clinical-trial question and a machine-learning question take the same shapes above; what differs is only which source the hits come from. Don't send a biomedical or life-science query to the open web on the assumption the corpus is arXiv-only — PubMed, bioRxiv, and medRxiv are the largest part of what `search_papers` reads.
- **When in doubt, include.** For any topic / method / comparison question, return the relevant _family_, not just the single best match — err toward keeping a plausibly-relevant paper rather than dropping it. The neighboring methods are part of a good answer; don't reason close work out just because one paper is the most exact match.
- **Follow the literature, and keep what you find.** The seminal source, the competing methods, the close neighbors are usually a hop away — use `related_papers`, and _include_ them, not just the first hit. Stopping at one good result is the most common way to leave the reader with half an answer.
- **Verify to exclude, not to gatekeep.** Use `read_paper` to rule a paper _out_ when a hard constraint clearly fails (wrong org/author, doesn't actually report the score). When a paper is plausibly relevant, lean toward keeping it rather than demanding proof.
- **Only drop the clearly off-topic.** Don't pad with papers you're confident are unrelated — but that's a high bar; most plausibly-relevant work should make the cut.

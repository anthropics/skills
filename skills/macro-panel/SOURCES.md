# Macro Panel — Master Sources Log

Full provenance for the panel's knowledge bases. Built 2026-06-07 by distilling **primary sources**
(books, shareholder/quarterly letters, essays, blogs, interviews, speeches) for each thinker. The
**exhaustive per-source list with every URL + reachability** lives in each skill's
`references/article-index.md` — this file is the manifest + the cross-cutting reachability notes.

> Educational use. Frameworks are distilled/paraphrased with attribution; quotes are excerpts.
> A lens is not gospel — every thinker here has been wrong or early (see each SKILL.md Caveats).

## Per-thinker source logs (full detail in the linked index)

| Skill | Primary source spine | Full log |
|---|---|---|
| `analytics-lyn-alden` | ~100 lynalden.com evergreen articles + monthly newsletters | `analytics-lyn-alden/references/article-index.md` |
| `analytics-ray-dalio` | *Principles for Navigating Big Debt Crises*; *Principles for Dealing with the Changing World Order*; *How the Economic Machine Works* (essay/video); Bridgewater research (*The All Weather Story*, *Engineering Targeted Returns and Risks*, *The Holy Grail of Investing*); *How Countries Go Broke* (2025); economicprinciples.org + LinkedIn/X essays | `analytics-ray-dalio/references/article-index.md` |
| `analytics-stanley-druckenmiller` | Lost Tree Club (2015); Sohn Conference talks; Real Vision; Bloomberg; *In Good Company* (Tangen); Hoover Institution; USC/Lone Tree speeches; CNBC appearances (no book) | `analytics-stanley-druckenmiller/references/article-index.md` |
| `analytics-lacy-hunt` | Hoisington *Quarterly Review & Outlook* (multi-year); MacroVoices, WealthTrack, Hidden Forces, Forward Guidance, Julia La Roche interviews; cited academic papers (Reinhart-Rogoff, Cecchetti, Checherita-Rother, Fisher) | `analytics-lacy-hunt/references/article-index.md` |
| `analytics-michael-pettis` | *Trade Wars Are Class Wars* (Pettis & Klein, 2020); *The Great Rebalancing* (2013); *The Volatility Machine* (2001); Carnegie "China Financial Markets" blog; Foreign Affairs / FT / Project Syndicate; X threads; Odd Lots / MacroVoices interviews | `analytics-michael-pettis/references/article-index.md` |
| `analytics-russell-napier` | *Anatomy of the Bear*; *The Solid Ground* newsletter (ERIC); The Market/NZZ, MacroVoices, Grant Williams, *In Good Company*, Meb Faber interviews; Library of Mistakes | `analytics-russell-napier/references/article-index.md` |
| `analytics-warren-buffett` | Berkshire Hathaway Chairman's letters 1977-2024; the Owner's Manual; annual-meeting Q&A; *The Superinvestors of Graham-and-Doddsville* (1984); Fortune essays (1977 inflation, 1999 stock market, 2008 "Buy American") | `analytics-warren-buffett/references/article-index.md` |

## Cross-cutting reachability notes (recorded at build time)

- **Dalio:** ~25 source URLs all HTTP 200. Four official economicprinciples.org/bridgewater PDFs
  resolve but serve compressed binary (not text-extractable) — substance captured via the matching
  animated videos + official landing pages; marked `[binary PDF]` in its index.
- **Druckenmiller:** 0 dead links; 7 URLs return 403 to automated fetch but are public in a browser
  (GuruFocus Lost Tree transcript, four CNBC pages, RealClearPolitics video, TraderLion) — covered via
  non-blocked mirrors (NBC Bay Area, podscripts, Substack/Medium copies). Logged in its index.
- **Hunt:** 2 hard 404s found and corrected (Hoisington filename variants `HIM2025Q4NP.pdf`,
  `HIM2026Q1.pdf`); AdvisorPerspectives 403s to bots, Seeking Alpha paywalled — alternates used.
- **Pettis:** 0 dead links; 7 sources paywalled/blocked (Foreign Affairs, Foreign Policy, IMF F&D,
  three X threads) captured via search snippets; direct fetches of Carnegie posts + Phenomenal World
  succeeded.
- **Napier:** 1 confirmed 404 (RealInvestmentAdvice blog → AdvisorPerspectives mirror); The Market/NZZ,
  ERIC/"Solid Ground", Grant Williams are metered/paywalled (free Marcellus mirrors logged).
- **Buffett:** 1 dead URL corrected (`ownersmanual.pdf` → `owners.html`); 7 bot-blocked/paywalled
  (Fortune 1977/1999, NYT 2008, Columbia 1984, CNBC archive) supplied via full-text mirrors; all
  Berkshire letters 200 OK.

## How to refresh

Each thinker's `05-current-views.md` is the time-decaying file. To update a "current" stance, re-fetch
that thinker's newest letter/interview (links in their `article-index.md`) and update only that file +
this log's date. The evergreen theme files (01-04) rarely need changes.

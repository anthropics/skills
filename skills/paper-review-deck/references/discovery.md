# Paper Discovery Mode

When no paper has been chosen yet, find candidates, let the user choose, then continue from Step 1 with the chosen paper.

## 1. Ask for constraints (bundled into the same message as the Step 0 questions)
- **Topic / keywords** — e.g. "legged robot sim-to-real", "BIM knowledge graph"
- **Constraints (optional)** — year range, whether public code is required, single/bundle (how many papers)
- **Anchor paper (optional)** — when the user wants a follow-on paper, as in "the paper that comes after RMA"

Do not re-ask what was already said. If only the topic is given, proceed with the defaults (last 5 years, no constraints, single) and say so in one line.

## 2. Search
A paper that continues from the previous talk is the most useful, so look at the context first.
1. **Check previous talks** — read the existing `*litnote.md` files in the save folder (or the same parent folder) and build a list of papers already covered. Exclude those from the candidates.
2. **alphaXiv search** — keyword search with `discover_papers`. Search 2–3 times with different phrasings (a single search captures only one angle).
3. **If there is an anchor paper** — find follow-up work that cites or improves on it, and recent papers by the same authors (`get_researcher_papers`).
4. **Recent and trending supplement** — if the topic is broad, check `get_hot_feed` for papers currently getting attention.
5. **Papers outside arXiv** — for fields that need venue-only or journal papers (construction, engineering, etc.), supplement with WebSearch.
6. **Quick check per candidate** — for the top candidates, check the abstract and whether a GitHub repo or project page exists. Code and demo availability strongly determine the quality of the talk material.

## 3. Present candidates (5–8 papers)
| # | Title (year) | One-line summary | Code | Demo | Difficulty | Why recommended |
|---|---|---|---|---|---|---|
| 1 | … (2024) | … | ✓ | ✓ | Mid | Directly addresses the limitation (…) of last week's RMA |

- Difficulty: high / mid / low relative to the audience background (Step 0)
- Why recommended: state the relationship to previous talks and the anchor paper first
- Links in the form `https://www.alphaxiv.org/abs/{id}`
- In **bundle mode**, below the table propose 1–2 "combinations that flow well together" with reasons (e.g. problem statement → solution → extension)
- At the very bottom, the top recommendation in one line

## 4. After selection
- Once the user chooses, go straight to Step 1. Do not ask for confirmation again.
- Whether to save to the alphaXiv library follows the answer given in Step 0. If saving, use `save_papers_to_folder` to put them in a folder named after the talk context (e.g. "{study group} {topic}").

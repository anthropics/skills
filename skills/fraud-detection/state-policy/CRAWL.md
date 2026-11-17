# State Medicaid policy crawl — loop instructions

Called from `/loop` (self-paced). Each tick: discover ONE state's Medicaid provider-policy index,
scrape its policy-PDF links in Chrome, write `<state>.json`, flip the checklist row.

## Per-tick steps

1. **Pick the next state.** Read `STATES.md`, find the first `[ ]` row. If none, the crawl is done —
   stop the loop.

2. **Discover the index URL.** Web-search: `<state name> Medicaid provider manual policy guidelines
   billing site:.gov`. The target is the state Medicaid agency's provider-manual / policy-guidelines
   index (NOT a CMS.gov or KFF summary page). Common patterns: `eMedNY` (NY), `TMHP` (TX),
   `Medi-Cal` (CA), `AHCA` (FL), `HHSC`, `DMAS`, `MassHealth`, `TennCare`, `AHCCCS`.

3. **Open it in Chrome and read the page.** Use `mcp__claude-in-chrome__navigate` +
   `get_page_text` (curl often 403s on state sites). Identify the policy/billing-guideline
   documents — look for: "Provider Manual", "Policy Guidelines", "Billing Guidelines",
   "Coverage Policy", "Clinical Coverage", "Provider Handbook", per-specialty PDFs.

4. **If the page is a hub** (links to per-specialty sub-pages), follow 2–3 of the most
   detector-relevant ones (Transportation/NEMT, Personal Care/HCBS, Physician, Pharmacy, DME) and
   capture those PDF links. Don't crawl exhaustively — ~10–20 docs per state is the target.

5. **Write `<state>.json`** (lowercase 2-letter, sibling to `ny.json`): same shape as `ny.json` —
   `name`, `kind:"state-policy"`, `state`, `index`, `fetchVia` (`"browser"` if curl 403s, else
   `"curl"`), `out:"policy/<st>"`, `docs:[{title, detector, url, pp}]`. Fill `url` with the actual
   PDF href when you found it; leave `null` if it needs a deeper click. Tag `detector` with the
   D-id(s) the doc would inform (D4/D15/D16/D19/D20/D23/D3).

6. **Update `STATES.md`**: flip `[ ]` → `[x]`, fill Index URL + PDF count + a one-line note
   (e.g. "TMHP portal, login-gated for fee schedules but manuals are public").

7. **Commit** `<state>.json` + `STATES.md` with message `state-policy: add <ST> scraper config`.
   Don't push every tick — push every ~5 states or when stopping.

## What NOT to do

- Don't download the PDFs in the loop — that's `fetch-reference.js`'s job once the configs exist.
- Don't try states that require login/registration for manuals — note "login-gated" and move on.
- Don't spend >5 min per state; if the site is a maze, capture the index URL + a note and move on.

## Output target

51 `<state>.json` configs + a filled `STATES.md`. Then `fetch-reference.js` gets ONE `state-policy`
handler that reads `state-policy/*.json` and fetches each `docs[].url` →
`data-cache/reference/<q>/policy/<state>/<slug>.{pdf,txt}`.

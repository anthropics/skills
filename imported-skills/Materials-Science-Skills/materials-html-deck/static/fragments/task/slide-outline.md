# Task: slide outline only

Produce a structured Chinese slide outline from the source material. If the user asks for a rendered deck, route to the HTML deck task and keep HTML as the only delivery format for this skill.

## Output format

Return a markdown or JSON outline containing:

- paper metadata (title, authors, journal/year/DOI if available),
- detected `paper_type` and `deck_type`,
- central argument or main message,
- slide-by-slide plan with:
  - slide number,
  - Chinese title (conclusion-style where possible),
  - slide purpose,
  - suggested layout/composition,
  - 2-4 concise bullets,
  - selected figure/table asset (if any),
  - Chinese caption and interpretation,
  - core takeaway sentence,
  - speaker note (optional).

Save the outline to `output/html_deck_outline_cn.md` or `output/html_deck_outline_cn.json`.

If the user later wants the rendered deck, reuse this outline with `scripts/build_deck.mjs`.

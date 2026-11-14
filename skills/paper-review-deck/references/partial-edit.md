# Partial Edit Mode

For changing only part of a deck that has already been built. Do not rerun from scratch — it takes time, and edits the user made by hand could be overwritten.

## Order
1. **Identify the target** — which deck (save folder), which page, what to change. If there is only one folder, or it is the deck from the previous conversation, do not ask.
2. **Read the latest versions** — re-read `PPT Text.md`, the deck, `Presenter Notes.md`, `Speaker Script.md`, `Media Sourcing Guide.md` and `Reproduction Notes.md` in the save folder. If the user has edited anything by hand, work on top of that.
3. **Edit the source** — change only the relevant slide in `PPT Text.md`. Leave the other slides untouched.
4. **Propagate to the derived documents** — apply the same page only to the deck, notes, script and sourcing guide.
   - If slides are **added, removed or reordered**: renumber every page in the script and notes, and fix the transition sentences on the neighboring pages too.
   - If new media is needed, add a placeholder box per the `media.md` rules plus a row in the sourcing guide.
   - If the script length changes, update the total estimated time at the top as well.
5. **Regenerate all 3 outputs** — rebuild **all** of HTML, PDF and PPTX with `scripts/deck/make_deck.py` (even a one-page change requires the page numbers and notes of all three files to match). If the script changed, the PPTX presenter notes are updated at this point too.
6. **Visual QA** — check only the changed page and the pages immediately before and after with `scripts/render_check.py --static --pages`.
7. **Report** — only, briefly: the changed page numbers, the changed files (including the 3 outputs), and whether pages were renumbered.

## Common requests
| Request | Handling |
|---|---|
| "Shorten the text on p.7" | Only p.7 of the manuscript, deck, notes and script |
| "Swap in Fig 4" | Extract the figure → save to `figures/` → replace in manuscript and deck, fix the stage-direction line in the script |
| "Add one slide" | Insert, renumber pages, fix transition sentences |
| "Just make the script shorter" | Edit the script only (the manuscript is unchanged, so the other files stay as they are) |
| "I got the video" | Check the file the user dropped in → replace the placeholder box with the real media, tick the sourcing guide |
| "I ran the reproduction / the results are in" | Check the results in `reproduction/` → replace the Repro box with the plot/table, update the row in Reproduction Notes |

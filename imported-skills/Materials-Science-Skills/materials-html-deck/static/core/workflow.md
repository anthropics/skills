# Workflow

1. Read the source paper, notes, data, or outline.
2. Classify `deck_type`, `paper_type`, `academic_style`, domain, and template.
3. Build a slide plan with one main claim per slide.
4. Select figures/tables that provide evidence; crop and label assets before
   deck generation.
5. Write a JSON outline with titles, bullets, takeaways, images, notes, and
   optional layout fields.
6. Run `scripts/build_deck.mjs` to create the HTML deck directory.
7. Let strict Playwright verification check every slide and write screenshots.
8. Review `qa_report.md`, `asset_manifest.json`, and rendered screenshots.
9. Deliver the HTML directory as the artifact.

Keep the deck browser-native. Do not add export steps to this workflow.

# HTML-First Academic Deck

Attribution: copied and trimmed from
`huashu-design/references/slide-decks.md`.

HTML is the source, preview, and delivery artifact. Generate a multi-file deck:

- `index.html` as the browser presentation shell.
- `slides/*.html` as independent 1920x1080 slide files.
- `shared/tokens.css` for the deck-wide visual grammar.
- `screenshots/*.png` from strict browser verification.

Use independent slide files by default. This keeps each slide debuggable,
parallelizable, and directly verifiable through Playwright without cross-slide
CSS contamination.

For decks with five or more slides, establish visual grammar before scaling the
full deck: cover/title treatment, action-title style, evidence placement,
figure sizing, footnote convention, color roles, and speaker-note density.

Do not load huashu video, voiceover, prototype, audio, web-style, brand-system,
or multi-direction consultant workflows into this academic deck route.

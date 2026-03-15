# Wardrobe AI

Your personal AI-powered style assistant. Upload outfit photos, get instant style analysis, and build a visual history of your wardrobe.

## What it does

- **Upload outfits** — drag & drop or take a photo directly from your phone
- **Background removal** — automatically isolates the outfit from the background (runs in-browser, no server needed)
- **AI style analysis** — Claude identifies your clothing items, color palette, fabrics, occasion fit, and gives you 3 actionable styling tips
- **Calendar view** — see what you wore on each day; photo date is read from EXIF metadata automatically
- **Wardrobe grid** — browse all your outfits, filter by occasion or season
- **Style DNA** — after a few uploads, see your dominant style, top colors, and versatility score
- **Morning dashboard** — rewear suggestions, upload streak nudges, and a quick view of today's outfit

## Tech stack

| Layer | Technology |
|---|---|
| Framework | Next.js 15 (App Router) |
| Language | TypeScript |
| Styling | Tailwind CSS |
| AI | Claude Opus 4.6 (vision) via Anthropic SDK |
| Background removal | @imgly/background-removal (WASM, client-side) |
| EXIF reading | exifr |
| Storage | IndexedDB (images) + localStorage (metadata) |

## Getting started

```bash
cp .env.local.example .env.local
# Add your Anthropic API key to .env.local
npm install
npm run dev
```

Open [http://localhost:3000](http://localhost:3000).

## Deploying to Vercel

1. Import `jordivalls/Stailas-repo` on [vercel.com/new](https://vercel.com/new)
2. Add environment variable: `ANTHROPIC_API_KEY`
4. Deploy

Every push to GitHub triggers an automatic redeploy.

## Project structure

```
├── src/
│   ├── app/
│   │   ├── page.tsx              # Morning dashboard
│   │   ├── upload/page.tsx       # Upload flow
│   │   ├── outfit/[id]/page.tsx  # Outfit detail & style card
│   │   ├── calendar/page.tsx     # Monthly calendar view
│   │   ├── wardrobe/page.tsx     # Wardrobe grid + Style DNA
│   │   └── api/analyze/route.ts  # Claude vision API route
│   ├── components/
│   │   └── Navigation.tsx
│   ├── hooks/
│   │   └── useOutfits.ts
│   └── lib/
│       ├── types.ts
│       ├── storage.ts            # IndexedDB + localStorage helpers
│       ├── exif.ts               # EXIF date extraction
│       └── styleDNA.ts           # Wardrobe statistics
└── vercel.json
```

## Notes

- All data is stored **locally on your device** (IndexedDB + localStorage). Outfits do not sync across devices.
- The background removal model (~40 MB) is downloaded from the @imgly CDN on first use.
- You need an [Anthropic API key](https://console.anthropic.com) to run the AI analysis.

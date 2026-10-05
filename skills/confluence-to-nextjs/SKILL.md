---
name: confluence-to-nextjs
description: Convert Atlassian Confluence pages to native Next.js App Router pages — fetch content via Confluence REST API v2, parse storage-format HTML into semantic JSX, build a knowledge base with table of contents, anchor navigation, and matching design system. Use this skill whenever the user mentions Confluence migration, converting Confluence docs to Next.js, building a KB site from Confluence content, or replacing Atlassian-hosted pages with a self-hosted knowledge base — even if they just say "move our docs off Confluence" or "build a KB app".
---

# confluence-to-nextjs

Migrate Atlassian Confluence documentation to a self-hosted Next.js knowledge base. Fetches pages via the Confluence REST API, converts HTML storage format to semantic JSX, and wires up anchor navigation and a sticky table of contents.

## When to use

- Replacing external Confluence URLs in a product site with internal `/kb` routes
- Building a public knowledge base from Confluence content
- Porting support docs, deployment guides, or product documentation to Next.js

Do NOT use for:
- Wiki content that changes frequently and needs real-time sync (use Confluence embed instead)
- Non-Confluence CMS sources (use a different migration approach)

## Step 1: Fetch Confluence content

Use the Confluence REST API v2 with a personal API token:

```bash
curl -u "user@example.com:ATATT3x..." \
  "https://your-org.atlassian.net/wiki/api/v2/pages/PAGE_ID?body-format=storage" \
  -o page.json
```

The `storage` format returns HTML with Confluence-specific tags (`<ac:structured-macro>`, `<ac:parameter>`, `<ri:attachment>`) that must be stripped and converted.

## Step 2: Storage format → JSX conversion rules

| Confluence HTML | JSX equivalent |
|----------------|---------------|
| `<h1>`, `<h2>`, `<h3>` with text | `<h1 id="slug">`, `<h2 id="slug">` (slugify for anchor nav) |
| `<ac:structured-macro ac:name="info">` | `<div className="info-callout">` |
| `<table>` | `<table className="kb-table">` |
| `<ac:link>` internal links | Remove or replace with external link |
| `<strong>`, `<em>`, `<code>` | Pass through as-is |
| `<ul>`, `<ol>`, `<li>` | Pass through as-is |

Slug generation for heading IDs:

```typescript
function slugify(text: string): string {
  return text.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
}
```

## Step 3: Page structure

Each knowledge base page follows this layout:

```tsx
// app/support-maintenance/page.tsx
import type { Metadata } from "next";
import { TableOfContents } from "@/components/toc";

export const metadata: Metadata = {
  title: "Support & Maintenance",
  description: "SLA tiers, response times, and maintenance windows.",
};

const tocItems = [
  { id: "definitions", label: "Definitions", level: 2 },
  { id: "standard-support-contract", label: "Standard Support", level: 2 },
  { id: "gold-support-contract", label: "Gold Support", level: 2 },
];

export default function SupportMaintenancePage() {
  return (
    <section className="section inner-hero">
      <div className="container section">
        <div className="article-layout">
          <div className="article-content">
            <h2 id="definitions">Definitions</h2>
            <p>...</p>
            <table className="kb-table">
              <thead><tr><th>Priority</th><th>Description</th></tr></thead>
              <tbody>...</tbody>
            </table>
          </div>
          <TableOfContents items={tocItems} />
        </div>
      </div>
    </section>
  );
}
```

## Step 4: Table of contents component

Sticky sidebar with `IntersectionObserver` for active heading tracking:

```tsx
"use client";

import { useEffect, useState } from "react";

interface TocItem { id: string; label: string; level: number; }

export function TableOfContents({ items }: { items: TocItem[] }) {
  const [active, setActive] = useState<string>("");

  useEffect(() => {
    const observers = items.map(({ id }) => {
      const el = document.getElementById(id);
      if (!el) return null;
      const obs = new IntersectionObserver(
        ([entry]) => { if (entry.isIntersecting) setActive(id); },
        { rootMargin: "-20% 0px -70% 0px" }
      );
      obs.observe(el);
      return obs;
    });
    return () => observers.forEach((o) => o?.disconnect());
  }, [items]);

  return (
    <nav className="toc-sidebar" aria-label="On this page">
      <p className="toc-title">On this page</p>
      <ul>
        {items.map(({ id, label, level }) => (
          <li key={id} className={`toc-item level-${level} ${active === id ? "active" : ""}`}>
            <a href={`#${id}`}>{label}</a>
          </li>
        ))}
      </ul>
    </nav>
  );
}
```

## Step 5: Update source URLs

Replace Confluence links across the product site with KB routes:

```typescript
// Before (in site-data.ts, pricing.ts, etc.)
discoverUrl: "https://your-org.atlassian.net/wiki/spaces/SPACE/pages/12345"

// After
discoverUrl: `${process.env.NEXT_PUBLIC_KB_URL ?? "https://kb.example.com"}/deployment-motions#docker`
```

Anchor IDs must match the `id` attributes on the converted headings.

## Step 6: KB app scaffold

Minimal Next.js app for the knowledge base:

```
apps/kb/
├── app/
│   ├── layout.tsx          # SiteHeader + SiteFooter + GA script
│   ├── page.tsx            # Article index / home
│   ├── robots.ts
│   ├── sitemap.ts
│   └── <article-slug>/
│       └── page.tsx        # One file per Confluence page
├── components/
│   ├── site-header.tsx
│   ├── site-footer.tsx
│   └── toc.tsx             # TableOfContents
├── lib/
│   └── kb-data.ts          # Article metadata array
├── __tests__/              # Vitest + RTL tests per page
├── Dockerfile
└── package.json
```

Add the app to CI and K8s following the `nextjs-monorepo-ci` and `k8s-nextjs-deploy` skills.

## Testing converted pages

Each page needs a Vitest test checking:
1. H1 heading renders
2. Key section headings exist with correct anchor IDs
3. Tables contain expected content
4. TOC renders

```typescript
import { render, screen } from "@testing-library/react";
import SupportMaintenancePage from "@/app/support-maintenance/page";

vi.mock("@/components/toc", () => ({
  TableOfContents: () => <nav data-testid="toc" />,
}));

it("renders standard support anchor", () => {
  render(<SupportMaintenancePage />);
  const h = screen.getByRole("heading", { name: /Standard Support Contract/ });
  expect(h.id).toBe("standard-support-contract");
});
```

When a heading appears at multiple levels (h2 + h3 with similar text), use `{ level: 2 }` in the query to avoid `Found multiple elements` errors.

## Example prompts

- *"I want to replace our Confluence KB with a self-hosted Next.js site. Where do I start?"*
- *"How do I fetch a Confluence page's content via the REST API?"*
- *"Show me how to convert a Confluence `<ac:structured-macro name='info'>` callout to JSX."*
- *"Generate the TableOfContents component with IntersectionObserver for active-section tracking."*
- *"Write a Vitest test for the support-maintenance KB page checking anchor IDs."*
- *"How do I replace Confluence URLs across the product site with internal KB routes?"*

## Related skills

- [`nextjs-monorepo-ci`](./nextjs-monorepo-ci/SKILL.md) — add the `apps/kb` Next.js app to the CI pipeline
- [`k8s-nextjs-deploy`](./k8s-nextjs-deploy/SKILL.md) — deploy the KB app to Kubernetes

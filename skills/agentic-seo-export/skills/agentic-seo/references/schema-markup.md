# Schema Markup — Structured Data Implementation Guide

## Why Schema Markup Matters

Schema markup (structured data) helps:
1. **Search engines** understand your content better
2. **Rich results** appear in SERPs (stars, FAQs, prices, etc.)
3. **AI systems** extract and cite your content accurately
4. **Voice search** find precise answers from your site

Schema does NOT directly boost rankings — it improves how you appear and get cited.

---

## Schema Types by Page

### Homepage / Brand
```json
{
  "@context": "https://schema.org",
  "@type": "Organization",
  "name": "Your Brand",
  "url": "https://yoursite.com",
  "logo": "https://yoursite.com/logo.png",
  "sameAs": [
    "https://twitter.com/yourbrand",
    "https://linkedin.com/company/yourbrand"
  ],
  "contactPoint": {
    "@type": "ContactPoint",
    "telephone": "+1-555-555-5555",
    "contactType": "customer service"
  }
}
```

### Blog Articles
```json
{
  "@context": "https://schema.org",
  "@type": "Article",
  "headline": "Your Article Title",
  "author": {
    "@type": "Person",
    "name": "Author Name",
    "url": "https://yoursite.com/author/name"
  },
  "datePublished": "2025-01-01",
  "dateModified": "2025-03-01",
  "image": "https://yoursite.com/image.jpg",
  "publisher": {
    "@type": "Organization",
    "name": "Your Brand",
    "logo": {"@type": "ImageObject", "url": "https://yoursite.com/logo.png"}
  }
}
```

### FAQ Pages / FAQ Sections
```json
{
  "@context": "https://schema.org",
  "@type": "FAQPage",
  "mainEntity": [
    {
      "@type": "Question",
      "name": "What is your return policy?",
      "acceptedAnswer": {
        "@type": "Answer",
        "text": "We offer 30-day returns on all items..."
      }
    }
  ]
}
```
**Note**: Add to ANY page with FAQ-style Q&A — blog posts, product pages, etc.

### Product Pages (E-commerce)
```json
{
  "@context": "https://schema.org",
  "@type": "Product",
  "name": "Product Name",
  "description": "Product description",
  "image": "https://yoursite.com/product.jpg",
  "brand": {"@type": "Brand", "name": "Your Brand"},
  "offers": {
    "@type": "Offer",
    "price": "29.99",
    "priceCurrency": "USD",
    "availability": "https://schema.org/InStock"
  },
  "aggregateRating": {
    "@type": "AggregateRating",
    "ratingValue": "4.5",
    "reviewCount": "127"
  }
}
```

### Local Business
```json
{
  "@context": "https://schema.org",
  "@type": "LocalBusiness",
  "name": "Business Name",
  "address": {
    "@type": "PostalAddress",
    "streetAddress": "123 Main St",
    "addressLocality": "City",
    "addressRegion": "CA",
    "postalCode": "90210",
    "addressCountry": "US"
  },
  "telephone": "+1-555-555-5555",
  "openingHours": ["Mo-Fr 09:00-17:00", "Sa 10:00-14:00"],
  "geo": {
    "@type": "GeoCoordinates",
    "latitude": 34.0522,
    "longitude": -118.2437
  },
  "priceRange": "$$",
  "aggregateRating": {
    "@type": "AggregateRating",
    "ratingValue": "4.8",
    "reviewCount": "312"
  }
}
```

### How-To Articles
```json
{
  "@context": "https://schema.org",
  "@type": "HowTo",
  "name": "How to Set Up Google Business Profile",
  "step": [
    {
      "@type": "HowToStep",
      "name": "Create your account",
      "text": "Go to business.google.com and sign in..."
    },
    {
      "@type": "HowToStep", 
      "name": "Verify your business",
      "text": "Choose verification method..."
    }
  ]
}
```

### Review/Comparison Pages
```json
{
  "@context": "https://schema.org",
  "@type": "ItemList",
  "name": "Best SEO Tools 2025",
  "itemListElement": [
    {
      "@type": "ListItem",
      "position": 1,
      "name": "Semrush",
      "url": "https://yoursite.com/reviews/semrush"
    },
    {
      "@type": "ListItem",
      "position": 2,
      "name": "Ahrefs",
      "url": "https://yoursite.com/reviews/ahrefs"
    }
  ]
}
```

### SaaS / Software
```json
{
  "@context": "https://schema.org",
  "@type": "SoftwareApplication",
  "name": "Your SaaS",
  "applicationCategory": "BusinessApplication",
  "operatingSystem": "Web",
  "offers": {
    "@type": "Offer",
    "price": "49.00",
    "priceCurrency": "USD"
  },
  "aggregateRating": {
    "@type": "AggregateRating",
    "ratingValue": "4.7",
    "reviewCount": "523"
  }
}
```

---

## Implementation Methods

### Option 1: JSON-LD (Recommended)
Place in `<head>` or anywhere in `<body>`:
```html
<script type="application/ld+json">
{ your schema here }
</script>
```

### Option 2: Google Tag Manager
- Add new tag → Custom HTML
- Paste JSON-LD script
- Trigger: page-specific (URL contains, etc.)
- Best for: adding schema without code deployment

### Option 3: CMS Plugins
- WordPress: Yoast SEO, Rank Math, Schema Pro
- Shopify: JSON-LD for SEO
- Webflow: Custom code embed

---

## Validation & Testing

1. **Google Rich Results Test**: https://search.google.com/test/rich-results
   - Enter URL or paste code
   - Shows which rich results you qualify for
   - Highlights errors and warnings

2. **Schema.org Validator**: https://validator.schema.org
   - Validates schema correctness
   - Not Google-specific

3. **Google Search Console**:
   - Enhancements tab → shows rich result status per page type
   - Errors, valid, valid with warnings
   - Track after implementation

---

## Schema for AI Visibility

AI systems (ChatGPT, Perplexity, etc.) use structured data to:
- Extract facts reliably
- Attribute information accurately
- Build knowledge graphs

**High-impact for AI:**
- `FAQPage` → AI uses Q&A format heavily
- `HowTo` → AI loves step-by-step
- `Article` with `author` + `datePublished` → signals recency + authorship
- `Organization` with `sameAs` → helps AI identify your brand accurately

**Tips:**
- Be specific and complete in schema values
- Match schema content exactly to visible page content
- Use `description` fields generously — AI reads these
- Add `speakable` schema for voice search / AI audio responses

---

## Priority Implementation Order

For a new site, implement in this order:

1. `Organization` (homepage)
2. `Article` or `BlogPosting` (all blog content)
3. `FAQPage` (add to any page with Q&A)
4. `BreadcrumbList` (all pages)
5. `Product` + `AggregateRating` (if e-commerce)
6. `LocalBusiness` (if local)
7. `HowTo` (how-to content)
8. `SoftwareApplication` (if SaaS)

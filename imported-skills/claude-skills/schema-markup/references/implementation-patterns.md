# Implementation Patterns

Copy-paste JSON-LD patterns for every common schema type. Replace ALL_CAPS placeholders with real values. Test at rich-results.google.com before deploying.

---

## Article (Blog Post)

```json
{
  "@context": "https://schema.org",
  "@type": "BlogPosting",
  "headline": "ARTICLE_TITLE_MAX_110_CHARS",
  "description": "ARTICLE_DESCRIPTION_150_TO_300_CHARS",
  "image": {
    "@type": "ImageObject",
    "url": "https://YOURDOMAIN.COM/images/ARTICLE_IMAGE.jpg",
    "width": 1200,
    "height": 630
  },
  "author": {
    "@type": "Person",
    "name": "AUTHOR_FULL_NAME",
    "url": "https://YOURDOMAIN.COM/author/AUTHOR_SLUG",
    "sameAs": "https://www.linkedin.com/in/AUTHOR_LINKEDIN"
  },
  "publisher": {
    "@type": "Organization",
    "name": "PUBLICATION_OR_COMPANY_NAME",
    "logo": {
      "@type": "ImageObject",
      "url": "https://YOURDOMAIN.COM/images/logo.png",
      "width": 250,
      "height": 60
    }
  },
  "datePublished": "YYYY-MM-DD",
  "dateModified": "YYYY-MM-DD",
  "url": "https://YOURDOMAIN.COM/blog/ARTICLE_SLUG",
  "mainEntityOfPage": {
    "@type": "WebPage",
    "@id": "https://YOURDOMAIN.COM/blog/ARTICLE_SLUG"
  }
}
```

---

## HowTo Guide

```json
{
  "@context": "https://schema.org",
  "@type": "HowTo",
  "name": "How to TASK_NAME",
  "description": "BRIEF_DESCRIPTION_OF_WHAT_IS_ACCOMPLISHED",
  "image": "https://YOURDOMAIN.COM/images/HOWTO_IMAGE.jpg",
  "totalTime": "PT30M",
  "tool": [
    {
      "@type": "HowToTool",
      "name": "TOOL_NAME_1"
    },
    {
      "@type": "HowToTool",
      "name": "TOOL_NAME_2"
    }
  ],
  "supply": [
    {
      "@type": "HowToSupply",
      "name": "SUPPLY_NAME_1"
    }
  ],
  "step": [
    {
      "@type": "HowToStep",
      "position": 1,
      "name": "STEP_1_TITLE",
      "text": "STEP_1_FULL_INSTRUCTIONS",
      "image": "https://YOURDOMAIN.COM/images/step-1.jpg"
    },
    {
      "@type": "HowToStep",
      "position": 2,
      "name": "STEP_2_TITLE",
      "text": "STEP_2_FULL_INSTRUCTIONS",
      "image": "https://YOURDOMAIN.COM/images/step-2.jpg"
    },
    {
      "@type": "HowToStep",
      "position": 3,
      "name": "STEP_3_TITLE",
      "text": "STEP_3_FULL_INSTRUCTIONS"
    }
  ]
}
```

**Note:** `totalTime` uses ISO 8601 duration. `PT30M` = 30 minutes. `PT1H30M` = 1 hour 30 minutes.

---

## FAQPage

```json
{
  "@context": "https://schema.org",
  "@type": "FAQPage",
  "mainEntity": [
    {
      "@type": "Question",
      "name": "FIRST_QUESTION_TEXT?",
      "acceptedAnswer": {
        "@type": "Answer",
        "text": "FIRST_ANSWER_TEXT. Keep answers complete but concise — this appears directly in search results."
      }
    },
    {
      "@type": "Question",
      "name": "SECOND_QUESTION_TEXT?",
      "acceptedAnswer": {
        "@type": "Answer",
        "text": "SECOND_ANSWER_TEXT."
      }
    },
    {
      "@type": "Question",
      "name": "THIRD_QUESTION_TEXT?",
      "acceptedAnswer": {
        "@type": "Answer",
        "text": "THIRD_ANSWER_TEXT."
      }
    }
  ]
}
```

**Note:** Add as many Question/Answer pairs as the page has. Google typically shows 3-5 in results.

---

## Product with Offers and Ratings

```json
{
  "@context": "https://schema.org",
  "@type": "Product",
  "name": "PRODUCT_NAME",
  "description": "PRODUCT_DESCRIPTION",
  "image": [
    "https://YOURDOMAIN.COM/images/product-front.jpg",
    "https://YOURDOMAIN.COM/images/product-side.jpg"
  ],
  "sku": "PRODUCT_SKU",
  "brand": {
    "@type": "Brand",
    "name": "BRAND_NAME"
  },
  "offers": {
    "@type": "Offer",
    "url": "https://YOURDOMAIN.COM/products/PRODUCT_SLUG",
    "priceCurrency": "USD",
    "price": 49.99,
    "priceValidUntil": "YYYY-MM-DD",
    "availability": "https://schema.org/InStock",
    "itemCondition": "https://schema.org/NewCondition",
    "seller": {
      "@type": "Organization",
      "name": "YOUR_STORE_NAME"
    }
  },
  "aggregateRating": {
    "@type": "AggregateRating",
    "ratingValue": 4.7,
    "reviewCount": 143,
    "bestRating": 5,
    "worstRating": 1
  }
}
```

**Availability options:**
- `https://schema.org/InStock`
- `https://schema.org/OutOfStock`
- `https://schema.org/PreOrder`
- `https://schema.org/Discontinued`

---

## Organization (Site-Wide, in Header Template)

```json
{
  "@context": "https://schema.org",
  "@type": "Organization",
  "name": "COMPANY_LEGAL_NAME",
  "url": "https://YOURDOMAIN.COM",
  "logo": {
    "@type": "ImageObject",
    "url": "https://YOURDOMAIN.COM/images/logo.png",
    "width": 250,
    "height": 60
  },
  "description": "COMPANY_DESCRIPTION_1_SENTENCE",
  "foundingDate": "YYYY",
  "sameAs": [
    "https://www.linkedin.com/company/YOUR_COMPANY",
    "https://twitter.com/YOUR_HANDLE",
    "https://www.facebook.com/YOUR_PAGE",
    "https://www.crunchbase.com/organization/YOUR_COMPANY",
    "https://www.wikidata.org/wiki/QXXXXXXX"
  ],
  "contactPoint": {
    "@type": "ContactPoint",
    "telephone": "+1-800-555-0100",
    "contactType": "customer service",
    "areaServed": "US",
    "availableLanguage": "English"
  }
}
```

---

## LocalBusiness

```json
{
  "@context": "https://schema.org",
  "@type": "LocalBusiness",
  "name": "BUSINESS_NAME",
  "image": "https://YOURDOMAIN.COM/images/storefront.jpg",
  "url": "https://YOURDOMAIN.COM",
  "telephone": "+1-555-555-5555",
  "priceRange": "$$",
  "address": {
    "@type": "PostalAddress",
    "streetAddress": "123 Main Street",
    "addressLocality": "City Name",
    "addressRegion": "ST",
    "postalCode": "12345",
    "addressCountry": "US"
  },
  "geo": {
    "@type": "GeoCoordinates",
    "latitude": 40.7128,
    "longitude": -74.0060
  },
  "openingHoursSpecification": [
    {
      "@type": "OpeningHoursSpecification",
      "dayOfWeek": ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"],
      "opens": "09:00",
      "closes": "17:00"
    },
    {
      "@type": "OpeningHoursSpecification",
      "dayOfWeek": "Saturday",
      "opens": "10:00",
      "closes": "14:00"
    }
  ],
  "aggregateRating": {
    "@type": "AggregateRating",
    "ratingValue": 4.6,
    "reviewCount": 87,
    "bestRating": 5
  }
}
```

---

## BreadcrumbList

```json
{
  "@context": "https://schema.org",
  "@type": "BreadcrumbList",
  "itemListElement": [
    {
      "@type": "ListItem",
      "position": 1,
      "name": "Home",
      "item": "https://YOURDOMAIN.COM"
    },
    {
      "@type": "ListItem",
      "position": 2,
      "name": "CATEGORY_NAME",
      "item": "https://YOURDOMAIN.COM/CATEGORY-SLUG"
    },
    {
      "@type": "ListItem",
      "position": 3,
      "name": "CURRENT_PAGE_TITLE",
      "item": "https://YOURDOMAIN.COM/CATEGORY-SLUG/PAGE-SLUG"
    }
  ]
}
```

---

## VideoObject

```json
{
  "@context": "https://schema.org",
  "@type": "VideoObject",
  "name": "VIDEO_TITLE",
  "description": "VIDEO_DESCRIPTION_FULL",
  "thumbnailUrl": "https://YOURDOMAIN.COM/images/video-thumbnail.jpg",
  "uploadDate": "YYYY-MM-DD",
  "duration": "PT12M30S",
  "contentUrl": "https://YOURDOMAIN.COM/videos/VIDEO_FILE.mp4",
  "embedUrl": "https://www.youtube.com/embed/VIDEO_ID",
  "interactionStatistic": {
    "@type": "InteractionCounter",
    "interactionType": "https://schema.org/WatchAction",
    "userInteractionCount": 5000
  },
  "hasPart": [
    {
      "@type": "Clip",
      "name": "Introduction",
      "startOffset": 0,
      "endOffset": 90,
      "url": "https://YOURDOMAIN.COM/video/VIDEO_SLUG#t=0"
    },
    {
      "@type": "Clip",
      "name": "KEY_SECTION_NAME",
      "startOffset": 180,
      "endOffset": 360,
      "url": "https://YOURDOMAIN.COM/video/VIDEO_SLUG#t=180"
    }
  ]
}
```

---

## Combined: Article + BreadcrumbList (Most Blog Posts)

Use two separate `<script>` tags on the same page:

```html
<script type="application/ld+json">
{
  "@context": "https://schema.org",
  "@type": "BlogPosting",
  "headline": "ARTICLE_TITLE",
  ...full Article schema...
}
</script>

<script type="application/ld+json">
{
  "@context": "https://schema.org",
  "@type": "BreadcrumbList",
  ...full BreadcrumbList schema...
}
</script>
```

Or combine into a single `@graph` array:

```html
<script type="application/ld+json">
{
  "@context": "https://schema.org",
  "@graph": [
    {
      "@type": "BlogPosting",
      ...
    },
    {
      "@type": "BreadcrumbList",
      ...
    }
  ]
}
</script>
```

Both approaches are valid. `@graph` is cleaner for sites with many schema types per page.

---

## WebSite (Homepage Only)

```json
{
  "@context": "https://schema.org",
  "@type": "WebSite",
  "url": "https://YOURDOMAIN.COM",
  "name": "SITE_NAME",
  "potentialAction": {
    "@type": "SearchAction",
    "target": {
      "@type": "EntryPoint",
      "urlTemplate": "https://YOURDOMAIN.COM/search?q={search_term_string}"
    },
    "query-input": "required name=search_term_string"
  }
}
```

**Note:** Only add this if you have a working internal search at the URL template path.

---

## Duration Format Reference (ISO 8601)

| Duration | ISO 8601 |
|----------|----------|
| 30 minutes | `PT30M` |
| 1 hour | `PT1H` |
| 1 hour 30 minutes | `PT1H30M` |
| 2 hours 15 minutes | `PT2H15M` |
| 5 minutes 30 seconds | `PT5M30S` |
| 12 minutes 30 seconds | `PT12M30S` |

## Availability Values Reference

Always use the full schema.org URL — not just the word.

| Status | Value |
|--------|-------|
| In stock | `https://schema.org/InStock` |
| Out of stock | `https://schema.org/OutOfStock` |
| Pre-order | `https://schema.org/PreOrder` |
| Back order | `https://schema.org/BackOrder` |
| Limited availability | `https://schema.org/LimitedAvailability` |
| Discontinued | `https://schema.org/Discontinued` |

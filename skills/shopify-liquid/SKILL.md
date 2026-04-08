---
name: shopify-liquid
description: Build and modify Shopify Online Store 2.0 themes using Liquid, section schemas, template JSON, and Shopify CLI. Use when the user works with .liquid files, Shopify themes, section schemas, Shopify CLI commands, or mentions Shopify theme development.
license: MIT
compatibility: Designed for Claude Code on macOS and Linux
---

# Shopify Liquid — Theme Development

Build and modify Shopify Online Store 2.0 themes with Liquid templating, section schemas, and safe deployment workflows.

## Theme Structure

```
theme/
├── layout/theme.liquid         # Base HTML wrapper (required)
├── templates/*.json            # Page composition (section order + saved settings)
├── sections/*.liquid           # Reusable modules with schema
├── snippets/*.liquid           # Reusable fragments ({% render 'name' %})
├── assets/                     # CSS, JS, images ({{ 'file' | asset_url }})
├── config/settings_schema.json # Global theme settings for Shopify Admin
��── locales/*.json              # i18n translations
```

## Section Anatomy

Every section follows this pattern:

```liquid
<section class="my-section">
  {% if section.settings.eyebrow != blank %}
    <span class="eyebrow">{{ section.settings.eyebrow }}</span>
  {% endif %}

  <h2>{{ section.settings.heading }}</h2>

  {% for block in section.blocks %}
    <div class="block-item" {{ block.shopify_attributes }}>
      <h3>{{ block.settings.title }}</h3>
      <p>{{ block.settings.text }}</p>
    </div>
  {% endfor %}
</section>

{% schema %}
{
  "name": "My Section",
  "settings": [
    { "type": "text", "id": "eyebrow", "label": "Eyebrow" },
    { "type": "text", "id": "heading", "label": "Heading", "default": "Section Title" }
  ],
  "blocks": [
    {
      "type": "item",
      "name": "Item",
      "settings": [
        { "type": "text", "id": "title", "label": "Title" },
        { "type": "textarea", "id": "text", "label": "Text" }
      ]
    }
  ],
  "presets": [
    { "name": "My Section" }
  ]
}
{% endschema %}
```

## Schema Setting Types

| Type | Usage | Notes |
|------|-------|-------|
| `text` | Single line input | |
| `textarea` | Multi-line input | |
| `richtext` | HTML editor | Returns HTML string |
| `image_picker` | Image from file library | Use with `image_url` filter |
| `product` | Product selector | Returns product object |
| `collection` | Collection selector | Returns collection object |
| `select` | Dropdown | Requires `options` array |
| `range` | Numeric slider | Requires `min`, `max`, `step` |
| `checkbox` | Boolean toggle | |
| `color` | Color picker | Returns hex string |
| `url` | URL input | |
| `header` | Section divider | Label only, no `id` |

Access: `section.settings.field_id` (section level), `block.settings.field_id` (block level)

## Template JSON

Templates define which sections appear on a page and their order:

```json
{
  "sections": {
    "hero": {
      "type": "hero-banner",
      "settings": {
        "heading": "Welcome"
      }
    },
    "features": {
      "type": "features-grid",
      "settings": {}
    }
  },
  "order": ["hero", "features"]
}
```

**CRITICAL:** Template JSON contains merchant-saved data (images, text overrides). Never push templates without pulling first — it erases merchant customizations.

## Layout File Pattern

```liquid
<!doctype html>
<html lang="{{ request.locale.iso_code }}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>{{ page_title }}{% if current_tags %} — {{ current_tags | join: ', ' }}{% endif %}</title>
  {{ 'theme.css' | asset_url | stylesheet_tag }}
  {{ content_for_header }}
</head>
<body>
  {% section 'header' %}
  <main>{{ content_for_layout }}</main>
  {% section 'footer' %}
  <script src="{{ 'theme.js' | asset_url }}" defer></script>
</body>
</html>
```

- `content_for_header` — required (Shopify analytics, editor JS)
- `content_for_layout` — where template sections render

## Common Liquid Filters

**Assets:**
- `{{ 'file.css' | asset_url }}` — CDN URL for theme asset
- `{{ image | image_url: width: 800 }}` — resized image URL
- `{{ 'key' | t }}` — i18n translation from locales

**Display:**
- `{{ price | money }}` — format as currency
- `{{ string | strip }}` — trim whitespace
- `{{ value | default: 'fallback' }}` — fallback if empty
- `{{ string | escape }}` — HTML escape
- `{{ string | truncate: 100 }}` — truncate with ellipsis

**Whitespace:** Use `{%- tag -%}` (hyphens) to strip surrounding whitespace.

## Shopify CLI Workflow

```bash
# Install
brew install shopify-cli

# Local dev (live preview, no live store affected)
shopify theme dev --store mystore.myshopify.com

# Pull remote changes (merchant edits) BEFORE pushing
shopify theme pull --store mystore.myshopify.com

# Safe push (sections + assets only, never delete remote files)
shopify theme push --store mystore.myshopify.com \
  --allow-live \
  --nodelete \
  --only "sections/*:assets/*:layout/*:snippets/*:locales/*:config/settings_schema.json"

# Push specific template (only when intentional)
shopify theme push --only "templates/page.about.json"

# Create new unpublished theme
shopify theme push --store mystore.myshopify.com --theme-name "New Theme"
```

**Flags:**
- `--allow-live` — update the live (published) theme
- `--nodelete` — don't remove files missing locally
- `--only` — colon-separated glob patterns (not comma)

## Common Gotchas

1. **image_picker crashes** — `image_url` filter on nil crashes silently. Always guard: `{% if section.settings.image != blank %}`

2. **Schema defaults ignored** — If template JSON has ANY saved settings for a section, ALL schema defaults are ignored. Design accordingly.

3. **CDN caching** — Shopify uses Cloudflare. Pushes don't purge cache. Merchant must save in theme editor to force refresh.

4. **Block shopify_attributes** — Always add `{{ block.shopify_attributes }}` to block wrapper divs. Without it, blocks can't be reordered/edited in the theme editor.

5. **Locale key fallback** — Missing translation keys render as the key string itself (e.g., `pages.home.hero.title` appears literally).

6. **Form handling** — Use `{%- form 'contact' -%}` for native Shopify forms. Submissions appear in Admin > Customers. Use `name="contact[body]"` for custom fields.

7. **Reveal animations in editor** — Sections with `opacity: 0` on load (reveal-on-scroll) won't show in the theme editor. Add: `{% if request.design_mode %}style="opacity:1"{% endif %}`

## i18n Pattern

Locale file (`locales/en.default.json`):
```json
{
  "sections": {
    "hero": {
      "eyebrow": "WELCOME",
      "heading": "Your Brand Here"
    }
  }
}
```

Usage: `{{ 'sections.hero.eyebrow' | t }}`

Locale-aware links:
```liquid
{%- assign base = request.locale.root_url -%}
{%- if base == '/' -%}{%- assign base = '' -%}{%- endif -%}
<a href="{{ base }}/products/my-product">Shop</a>
```

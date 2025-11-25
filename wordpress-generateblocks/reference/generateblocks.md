---

# GenerateBlocks & GeneratePress Expert Guide

## Tech Stack
- **Theme**: GeneratePress 3.6.0
- **Premium Plugin**: GP Premium 2.5.5
- **Blocks**: GenerateBlocks 2.1.2 + GenerateBlocks Pro 2.4.0
- **WordPress**: 6.6+

---

## GenerateBlocks Core Blocks

### 1. Element (Container)
The foundational block - replaces the old Container block.

**HTML Tags Available**:
- Semantic: `section`, `article`, `aside`, `header`, `footer`, `nav`, `main`, `figure`
- Generic: `div`, `span`
- Lists: `ul`, `ol`, `li`, `dl`, `dt`, `dd`
- Link: `a`

**Key Attributes**:
```javascript
{
  uniqueId: "unique-identifier",
  tagName: "section",
  styles: {
    display: "flex",
    flexDirection: "column",
    gap: "2rem",
    padding: { top: "4rem", bottom: "4rem" },
    backgroundColor: "var(--contrast-3)",
    minHeight: "100vh"
  },
  htmlAttributes: {
    id: "hero-section",
    "data-section": "hero"
  }
}
```

**Hero Section Pattern**:
```
Element (section)
├── styles: { minHeight: '100vh', display: 'flex', alignItems: 'center' }
├── Element (div.container)
│   ├── Text (h1) - Hero Title
│   ├── Text (p) - Subtitle
│   └── Text (a.button) - CTA
```

**Grid Layout Pattern**:
```
Element (section)
├── Element (div.grid)
│   ├── styles: { display: 'grid', gridTemplateColumns: 'repeat(3, 1fr)', gap: '2rem' }
│   ├── Element (div.card) - Item 1
│   ├── Element (div.card) - Item 2
│   └── Element (div.card) - Item 3
```

### 2. Text Block
Rich text content with advanced typography control.

**HTML Tags**: `p`, `span`, `div`, `h1`-`h6`, `a`, `button`, `figcaption`, `li`

**Key Features**:
- Icon support (before/after text)
- Icon-only mode
- Dynamic content (post title, excerpt, meta, etc.)
- Link wrapper with aria-label

**Example**:
```javascript
{
  tagName: "h2",
  content: "{{ post:title }}",
  icon: "<svg>...</svg>",
  iconLocation: "before",
  styles: {
    fontSize: "2.5rem",
    fontWeight: "700",
    color: "var(--contrast)",
    marginBottom: "1rem"
  }
}
```

### 3. Media (Image)
Optimized image blocks with link support.

**Key Attributes**:
```javascript
{
  mediaId: 123,
  linkHtmlAttributes: {
    href: "/page",
    target: "_blank",
    rel: "noopener"
  },
  styles: {
    borderRadius: "0.5rem",
    objectFit: "cover",
    aspectRatio: "16/9"
  }
}
```

### 4. Query Block
Display posts dynamically using WP_Query.

**Query Parameters**:
```javascript
{
  query: {
    postType: "post",
    postsPerPage: 6,
    orderby: "date",
    order: "DESC",
    taxQuery: [{
      taxonomy: "category",
      terms: [5, 10]
    }]
  },
  pagination: "standard"
}
```

**Blog Posts Query Loop Pattern**:
```
Query
├── query: { postType: 'post', postsPerPage: 9, orderby: 'date' }
├── Element (div.posts-grid)
│   ├── styles: { display: 'grid', gridTemplateColumns: 'repeat(auto-fill, minmax(300px, 1fr))', gap: '2rem' }
│   └── Loop Item
│       └── Element (article.post-card)
│           ├── Media - {{ post:featured-image }}
│           ├── Element (div.post-content)
│           │   ├── Text (h3) - {{ post:title }}
│           │   ├── Text (div.meta) - {{ post:date }}
│           │   └── Text (p) - {{ post:excerpt }}
└── Query Page Numbers
```

### 5. Shape Block
SVG shapes and icons for dividers and decorative elements.

---

## GenerateBlocks Pro Features

### Navigation Block
Complete navigation system with mega menus.

**Components**:
- **Navigation** - Main container
- **Menu Container** - Menu wrapper
- **Menu Toggle** - Mobile hamburger
- **Classic Menu** - WordPress menu
- **Classic Menu Item** - Individual items
- **Classic Sub Menu** - Dropdowns

**Mega Menu Pattern**:
```
Navigation
├── Classic Menu
│   ├── Classic Menu Item "Products"
│   │   └── Classic Sub Menu (mega menu)
│   │       └── Element (grid with 4 columns)
│   │           ├── Element (category 1)
│   │           ├── Element (category 2)
│   │           └── ...
```

### Site Header Block
Sticky, dynamic headers.

**Pattern**:
```
Site Header (sticky)
├── Element (div.header-inner)
│   ├── Media (logo)
│   ├── Navigation (main menu)
│   └── Element (div.header-actions)
│       ├── Text (search icon)
│       └── Text (button "Get Started")
```

### Tabs Component
```
Tabs
├── Tabs Menu
│   ├── Tab Menu Item "Tab 1"
│   ├── Tab Menu Item "Tab 2"
│   └── Tab Menu Item "Tab 3"
└── Tab Items
    ├── Tab Item (Content 1)
    ├── Tab Item (Content 2)
    └── Tab Item (Content 3)
```

### Accordion Component
```
Accordion
├── Accordion Item
│   ├── Accordion Toggle
│   │   ├── Text "Question 1"
│   │   └── Accordion Toggle Icon
│   └── Accordion Content
│       └── Text "Answer..."
```

### Overlay Panel System
Modals, off-canvas panels, mega menus.

**Types**: Modal (center), Slide-in (side), Full-screen, Anchored

**Triggers**: Click, Scroll position, Time delay, Exit intent, URL parameter

**Example Modal**:
```javascript
// Trigger element
Text (button)
├── htmlAttributes: { "data-overlay-trigger": "contact-modal" }
```

### Conditions System
Show/hide blocks based on rules:
- Location (page/post/archive)
- User Role
- Date/Time
- Device (desktop/mobile/tablet)
- Query Args (URL parameters)
- Post Meta, User Meta, Cookie, Language, Referrer

### Device Visibility (Pro)
```javascript
{
  hideOnDesktop: false,
  hideOnTablet: false,
  hideOnMobile: true
}
```

---

## GP Premium Modules

### Elements System
Create reusable header, footer, and hook content using GenerateBlocks.

**Element Types**: Header, Footer, Hook, Layout, Block

**Display Rules**: Entire site, Specific post types, Individual posts/pages, Archives, User roles

---

## GP Premium Block Elements (Hook) - CRITICAL

### Creating Block Elements via PHP/WP-CLI

Block Elements use TWO meta keys for type identification:

1. `_generate_element_type` = `'block'` → Triggers `GeneratePress_Block_Element` class
2. `_generate_block_type` = `'hook'` → Specifies the block element subtype

**WRONG (won't work):**
```php
update_post_meta($id, '_generate_element_type', 'hook');  // Legacy Hook Element
```

**CORRECT:**
```php
update_post_meta($id, '_generate_element_type', 'block');  // Block Element
update_post_meta($id, '_generate_block_type', 'hook');     // Hook subtype
```

### Block Element Meta Keys Reference

```php
// Required meta keys for Block Element Hook:
update_post_meta($element_id, '_generate_element_type', 'block');
update_post_meta($element_id, '_generate_block_type', 'hook');
update_post_meta($element_id, '_generate_hook', 'generate_before_header');
update_post_meta($element_id, '_generate_hook_priority', '5');

// Display conditions (array format)
update_post_meta($element_id, '_generate_element_display_conditions', array(
    array('rule' => 'general:site')  // Entire site
));

// Optional
update_post_meta($element_id, '_generate_element_exclude_conditions', array());
update_post_meta($element_id, '_generate_element_user_conditions', array());
```

### Available Hook Locations

**Before Header:**
- `generate_before_header` - Before entire header (perfect for Top Bar)
- `wp_body_open` - Very first hook after `<body>`

**Header Area:**
- `generate_before_header_content` - Inside header, before content
- `generate_after_header_content` - Inside header, after content
- `generate_after_header` - After entire header

**Content Area:**
- `generate_before_main_content` - Before main content
- `generate_after_main_content` - After main content
- `generate_before_content` - Before entry content
- `generate_after_content` - After entry content

**Footer Area:**
- `generate_before_footer` - Before footer
- `generate_after_footer` - After footer
- `generate_footer_widgets` - Footer widget area

### Block Type Values for `_generate_block_type`

| Value | Description | Auto Hook |
|-------|-------------|-----------|
| `hook` | Custom hook location | Uses `_generate_hook` |
| `site-header` | Replaces site header | `generate_header` |
| `site-footer` | Replaces site footer | `generate_footer` |
| `right-sidebar` | Right sidebar content | `generate_before_right_sidebar_content` |
| `left-sidebar` | Left sidebar content | `generate_before_left_sidebar_content` |
| `content-template` | Post/page template | `generate_before_do_template_part` |
| `loop-template` | Archive loop template | `generate_before_main_content` |
| `search-modal` | Search modal content | `generate_inside_search_modal` |

### Complete Example: Creating a Top Bar Element

```php
<?php
require_once('/var/www/html/wp-load.php');

// GenerateBlocks content for Top Bar
$topbar_content = '<!-- wp:generateblocks/element {"uniqueId":"topbar01","tagName":"div","styles":{"backgroundColor":"#80b238","paddingTop":"0.5rem","paddingBottom":"0.5rem"},"css":".gb-element-topbar01{background-color:#80b238;padding-top:0.5rem;padding-bottom:0.5rem}"} -->
<div class="gb-element gb-element-topbar01">
<!-- wp:generateblocks/element {"uniqueId":"topbar02","tagName":"div","styles":{"maxWidth":"1280px","marginLeft":"auto","marginRight":"auto","paddingLeft":"1.5rem","paddingRight":"1.5rem","display":"flex","justifyContent":"space-between","alignItems":"center"},"css":".gb-element-topbar02{max-width:1280px;margin-left:auto;margin-right:auto;padding-left:1.5rem;padding-right:1.5rem;display:flex;justify-content:space-between;align-items:center}"} -->
<div class="gb-element gb-element-topbar02">
<!-- wp:generateblocks/text {"uniqueId":"topbar03","tagName":"a","styles":{"color":"#ffffff","fontSize":"0.875rem","textDecoration":"none"},"css":".gb-text-topbar03{color:#ffffff;font-size:0.875rem;text-decoration:none}"} -->
<a class="gb-text gb-text-topbar03" href="mailto:info@example.com">📧 info@example.com</a>
<!-- /wp:generateblocks/text -->
</div>
<!-- /wp:generateblocks/element -->
</div>
<!-- /wp:generateblocks/element -->';

// Create the Block Element
$element_id = wp_insert_post(array(
    'post_title' => 'Top Bar',
    'post_content' => $topbar_content,
    'post_status' => 'publish',
    'post_type' => 'gp_elements'
));

// CRITICAL: Set BOTH type meta keys
update_post_meta($element_id, '_generate_element_type', 'block');
update_post_meta($element_id, '_generate_block_type', 'hook');
update_post_meta($element_id, '_generate_hook', 'generate_before_header');
update_post_meta($element_id, '_generate_hook_priority', '5');
update_post_meta($element_id, '_generate_element_display_conditions', array(
    array('rule' => 'general:site')
));
```

### CSS Generation for Block Elements

GenerateBlocks CSS is NOT automatically generated for Block Elements created via PHP/CLI.

**Solution 1: Include CSS in block attributes**
```javascript
{
  "uniqueId": "topbar01",
  "css": ".gb-element-topbar01{background-color:#80b238;padding:0.5rem}"
}
```

**Solution 2: Append CSS to existing GenerateBlocks stylesheet**
```php
$upload_dir = wp_upload_dir();
$css_file = $upload_dir['basedir'] . '/generateblocks/style-57.css';
$topbar_css = '.gb-element-topbar01{background-color:#80b238}';
file_put_contents($css_file, file_get_contents($css_file) . $topbar_css);
```

**Solution 3: Open element in WordPress editor and save**
This triggers the block parser to generate CSS automatically.

### Display Condition Rules

```php
// Entire site
array('rule' => 'general:site')

// Specific page
array('rule' => 'general:singular', 'object' => 123)

// All posts
array('rule' => 'post:post')

// All pages
array('rule' => 'post:page')

// Front page
array('rule' => 'general:front_page')

// Blog page
array('rule' => 'general:blog')

// Archives
array('rule' => 'archive:post')  // Post archives
array('rule' => 'archive:category')  // Category archives

// 404 page
array('rule' => 'general:404')

// Search results
array('rule' => 'general:search')
```

### Typography System
Complete control over all text via Customizer:
- Font family, weight, style
- Font size (responsive)
- Line height, letter spacing
- Text transform, decoration

### Colors System
Global color palette variables:
```css
--contrast: #222222      /* Main text */
--contrast-2: #575760    /* Secondary text */
--contrast-3: #b2b2be    /* Tertiary text */
--base: #f0f0f0          /* Light backgrounds */
--base-2: #f7f8f9        /* Lighter backgrounds */
--base-3: #ffffff        /* White */
--accent: #1e73be        /* Primary color */
```

**Usage in GenerateBlocks**:
```javascript
styles: {
  backgroundColor: "var(--base-2)",
  color: "var(--contrast)",
  borderColor: "var(--accent)"
}
```

### Other Modules
- **Secondary Navigation** - Additional menus
- **Blog Module** - Advanced blog styling
- **Sections** - Full-width backgrounds with parallax
- **Menu Plus** - Advanced menu features, mega menus
- **WooCommerce** - Deep WooCommerce integration
- **Backgrounds** - Multiple backgrounds, gradients, blend modes
- **Spacing Module** - Precise spacing control

---

## Critical: Full-Width Sections Architecture

### The Problem
GenerateBlocks sections are constrained by theme container width by default.

### The Solution: Two-Layer Architecture

**ALWAYS use this pattern:**

```html
<!-- OUTER LAYER: Full-width background -->
<section class="gbp-section gb-element-{uniqueId}">
  <!-- INNER LAYER: Centered content -->
  <div class="gbp-section__inner gb-element-{uniqueId}">
    <!-- Your content here -->
  </div>
</section>
```

### GenerateBlocks Implementation

**Outer Section (Full-Width Background)**:
```javascript
{
  uniqueId: "hero001",
  tagName: "section",
  styles: {
    backgroundColor: "#f0fdf4",
    paddingTop: "4rem",
    paddingBottom: "4rem"
  },
  globalClasses: ["gbp-section"]
}
```

**Inner Container (Centered Content)**:
```javascript
{
  uniqueId: "hero002",
  tagName: "div",
  styles: {
    marginLeft: "auto",
    marginRight: "auto",
    maxWidth: "1280px",
    paddingLeft: "1.5rem",
    paddingRight: "1.5rem"
  },
  globalClasses: ["gbp-section__inner"]
}
```

### Required CSS (CRITICAL!)

```css
/* Force sections to 100% viewport width */
.page-id-57 .gbp-section {
  max-width: none !important;
  width: 100vw !important;
  margin-left: calc(50% - 50vw) !important;
  margin-right: calc(50% - 50vw) !important;
  padding-left: 0 !important;
  padding-right: 0 !important;
}

/* Constrain inner content */
.page-id-57 .gbp-section__inner {
  max-width: 1280px !important;
  margin-left: auto !important;
  margin-right: auto !important;
  padding-left: 1.5rem !important;
  padding-right: 1.5rem !important;
}
```

### Page Meta Requirements

```bash
wp post meta update PAGE_ID _generate-full-width-content true --allow-root
wp post meta update PAGE_ID _generate-sidebar-layout-meta no-sidebar --allow-root
wp post meta update PAGE_ID _generate-disable-headline true --allow-root
```

### Common Mistake - DON'T DO THIS:
```javascript
// Using contentSize layout constraint on outer section
layout: {
  type: "constrained",
  contentSize: "1280px"  // This prevents full-width!
}
```

---

## Block Parser Requirements

**CRITICAL**: GenerateBlocks generates CSS from block attributes at save time, not render time.

- ✅ **Saving via WordPress Editor** → Triggers parser → Generates CSS
- ❌ **WP-CLI `wp post update`** → Does NOT trigger parser → NO CSS

**Workflow for WP-CLI content**:
1. Update content via WP-CLI
2. Open WordPress editor and click "Update"
3. This triggers block parser to generate CSS

**Always provide fallback CSS** in child theme for blocks that haven't been parsed yet.

---

## Dynamic Content Tags

### Free Version
- `{{ post:title }}` - Post title
- `{{ post:excerpt }}` - Post excerpt
- `{{ post:permalink }}` - Post URL
- `{{ post:date }}` - Publish date
- `{{ post:featured-image }}` - Featured image
- `{{ post:author-name }}` - Author name
- `{{ post:author-url }}` - Author archive URL
- `{{ post:comment-count }}` - Number of comments
- `{{ post:terms }}` - Categories/tags
- `{{ site:url }}` - Site URL
- `{{ site:title }}` - Site title

### Pro Tags
- `{{ archive:title }}` - Archive title
- `{{ archive:description }}` - Archive description
- `{{ option:option-name }}` - Site option
- `{{ user:meta }}` - Current user meta
- `{{ current:year }}` - Current year
- `{{ loop:index }}` - Loop iteration number

---

## Common Design Patterns

### Full-Width Hero with CTA
```
Element (section.hero)
├── styles: { minHeight: '100vh', display: 'flex', alignItems: 'center', backgroundImage: 'url(...)', backgroundSize: 'cover' }
├── Element (div.container)
│   ├── styles: { maxWidth: '1200px', margin: '0 auto', padding: '2rem' }
│   ├── Text (h1) - styles: { fontSize: '3rem', fontWeight: '700', color: '#fff' }
│   ├── Text (p) - styles: { fontSize: '1.25rem', color: 'rgba(255,255,255,0.9)' }
│   └── Text (a.button) - styles: { display: 'inline-block', padding: '1rem 2rem', backgroundColor: 'var(--accent)', color: '#fff', borderRadius: '0.5rem' }
```

### Three-Column Feature Grid
```
Element (section.features)
├── styles: { padding: { top: '5rem', bottom: '5rem' } }
├── Element (div.container)
│   ├── Text (h2) - styles: { textAlign: 'center', marginBottom: '3rem' }
│   └── Element (div.grid)
│       ├── styles: { display: 'grid', gridTemplateColumns: 'repeat(3, 1fr)', gap: '2rem' }
│       ├── Element (div.feature-card)
│       │   ├── Shape (icon)
│       │   ├── Text (h3)
│       │   └── Text (p)
│       ├── Element (div.feature-card)
│       └── Element (div.feature-card)
```

### Sticky Header with Logo and Nav
```
Site Header
├── sticky: true
├── styles: { backgroundColor: 'var(--base-3)', boxShadow: '0 2px 4px rgba(0,0,0,0.1)' }
└── Element (div.header-inner)
    ├── styles: { display: 'flex', justifyContent: 'space-between', alignItems: 'center', maxWidth: '1200px', margin: '0 auto', padding: '1rem 2rem' }
    ├── Media (logo) - styles: { height: '50px' }
    └── Navigation
        └── Classic Menu
```

### Accordion FAQ Section
```
Element (section.faq)
├── styles: { padding: { top: '4rem', bottom: '4rem' } }
├── Element (div.container)
│   ├── Text (h2) - styles: { textAlign: 'center', marginBottom: '2rem' }
│   └── Accordion
│       ├── Accordion Item
│       │   ├── Accordion Toggle
│       │   │   ├── Text "Question?"
│       │   │   └── Accordion Toggle Icon
│       │   └── Accordion Content
│       │       └── Text "Answer..."
```

---

## Responsive Design

### Breakpoints
- **Desktop**: 1025px and above
- **Tablet**: 768px to 1024px
- **Mobile**: 767px and below

### Responsive Styles
```javascript
styles: {
  // Desktop (default)
  fontSize: "2rem",
  padding: { top: "4rem", right: "2rem", bottom: "4rem", left: "2rem" },

  // Tablet
  fontSizeTablet: "1.5rem",
  paddingTablet: { top: "3rem", right: "1.5rem", bottom: "3rem", left: "1.5rem" },

  // Mobile
  fontSizeMobile: "1.25rem",
  paddingMobile: { top: "2rem", right: "1rem", bottom: "2rem", left: "1rem" }
}
```

### Responsive Grid (No Media Queries)
```css
.feature-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
  gap: 2rem;
}
```

---

## Video Embeds: 16:9 Container

**Required CSS**:
```css
.video-container {
  position: relative !important;
  padding-bottom: 56.25% !important;  /* 16:9 ratio */
  height: 0 !important;
  overflow: hidden !important;
}

.video-container iframe {
  position: absolute !important;
  top: 0 !important;
  left: 0 !important;
  width: 100% !important;
  height: 100% !important;
}
```

---

## Grid Layouts

### 2/3 + 1/3 Column Pattern
```javascript
// Grid Container
{
  styles: {
    display: "grid",
    gridTemplateColumns: "repeat(3, minmax(0, 1fr))",
    columnGap: "3rem",
    "@media (max-width:1024px)": {
      gridTemplateColumns: "1fr"
    }
  }
}

// Left Column (2/3)
{
  styles: {
    gridColumn: "span 2 / span 2",
    "@media (max-width:1024px)": {
      gridColumn: "span 1 / span 1"
    }
  }
}
```

---

## CSS Classes Reference

### Core Classes
```css
.gb-element              /* Element block */
.gb-text                 /* Text block */
.gb-media                /* Media block */
.gb-container            /* Legacy container */
.gb-grid-wrapper         /* Legacy grid */
.gb-button               /* Legacy button */
```

### State Classes
```css
.gb-block-is-current     /* Active/current state */
.gb-is-sticky            /* Sticky header */
.gb-overlay-open         /* When overlay is open */
```

### Layout Classes
```css
.gb-inside-container     /* Inner container wrapper */
.gb-grid-column          /* Grid column item */
.gb-query-loop-wrapper   /* Query container */
.gb-query-loop-item      /* Loop item */
```

---

## ACF Integration (Pro 1.4.0+)

### Supported Field Types
- Basic: Text, Textarea, Number, Email, URL
- Content: WYSIWYG, oEmbed, Image, File, Gallery
- Choice: Select, Checkbox, Radio, True/False
- Relational: Link, Post Object, Relationship, Taxonomy

### Usage
```javascript
// In Text Block
{
  content: "{{ post:meta key:field_name }}"
}

// In Query Loop Item
{
  content: "{{ loop_item key:acf_field_name }}"
}
```

---

## Performance Best Practices

1. **Use Element blocks** instead of legacy Container
2. **Minimize inline styles** - Use global styles
3. **Optimize images** - WebP, lazy loading, proper sizes
4. **Limit query complexity** - Only query needed fields
5. **Use conditions wisely** - Don't overuse
6. **Cache overlays** - Automatically cached in Pro
7. **Test responsive** - Check all breakpoints
8. **Minimize nesting** - Keep hierarchy shallow

---

## Common Pitfalls to Avoid

1. ❌ Don't nest too many containers
2. ❌ Don't use inline styles for everything
3. ❌ Don't forget mobile styles
4. ❌ Don't overuse conditions
5. ❌ Don't ignore semantic HTML
6. ❌ Don't duplicate layouts - use patterns
7. ❌ Don't forget accessibility
8. ❌ Don't mix legacy and modern blocks

---

## Debugging Tips

### Check Block Attributes (Browser Console)
```javascript
wp.data.select('core/block-editor').getSelectedBlock()
```

### View Generated CSS
Check `<style>` tags with ID containing `generateblocks-style`

### Display Rules Not Working
1. Check condition post is published
2. Verify display rules are saved
3. Test as different user roles
4. Clear cache

### Overlay Not Opening
1. Check trigger has correct `data-overlay-trigger`
2. Verify overlay panel ID matches
3. Check for JS errors in console
4. Ensure GenerateBlocks Pro is active

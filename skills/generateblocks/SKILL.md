---
name: generateblocks
description: GenerateBlocks plugin development expert for creating layouts, components, and dynamic content with GenerateBlocks and GenerateBlocks Pro. Use when working with GB Container, Grid, Headline, Button, Image blocks, Query Loop, Dynamic Data, Local/Global Styles, Block Patterns, or any GenerateBlocks-specific development task.
---

# GenerateBlocks Development Guide

Expert guidance for building with GenerateBlocks - lightweight, flexible blocks for WordPress.

## Core Blocks

### Container Block

The foundation block for layouts and sections.

```html
<!-- Basic container -->
<!-- wp:generateblocks/container {"uniqueId":"14efce1c","paddingTop":"40","paddingRight":"40","paddingBottom":"40","paddingLeft":"40"} -->
<div class="gb-container gb-container-14efce1c">
    <!-- Inner content -->
</div>
<!-- /wp:generateblocks/container -->

<!-- Full-width section -->
<!-- wp:generateblocks/container {"uniqueId":"dfc37a3d","isGrid":true,"width":100,"widthMobile":100,"align":"full"} -->
<div class="gb-container gb-container-dfc37a3d alignfull">
    <!-- Inner content -->
</div>
<!-- /wp:generateblocks/container -->
```

**Key Attributes:**
- `tagName`: HTML tag (div, section, article, aside, header, footer)
- `isGrid`: Enable Flexbox layout
- `width`, `widthTablet`, `widthMobile`: Responsive widths
- `paddingTop/Right/Bottom/Left`: Padding values with units
- `marginTop/Right/Bottom/Left`: Margin values
- `backgroundColor`: Background color
- `gradient`: CSS gradient
- `bgImage`: Background image
- `borderRadius`: Border radius values
- `zIndex`: Z-index for stacking

### Grid Block

CSS Grid layout system.

```html
<!-- wp:generateblocks/grid {"uniqueId":"cc382b85","horizontalGap":"30","verticalGap":"30"} -->
<div class="gb-grid-wrapper gb-grid-wrapper-cc382b85">
    <!-- wp:generateblocks/container {"uniqueId":"9de1c95d","isGrid":true,"gridColumn":"span 6"} -->
    <div class="gb-container">Column 1</div>
    <!-- /wp:generateblocks/container -->

    <!-- wp:generateblocks/container {"uniqueId":"1c78ca88","isGrid":true,"gridColumn":"span 6"} -->
    <div class="gb-container">Column 2</div>
    <!-- /wp:generateblocks/container -->
</div>
<!-- /wp:generateblocks/grid -->
```

**Grid Attributes:**
- `horizontalGap`: Column gap
- `verticalGap`: Row gap
- `horizontalAlignment`: justify-items
- `verticalAlignment`: align-items

### Button Block

Buttons and button groups.

```html
<!-- wp:generateblocks/button-container {"uniqueId":"1b566f67"} -->
<div class="gb-button-wrapper gb-button-wrapper-1b566f67">
    <!-- wp:generateblocks/button {"uniqueId":"a3525e9a","backgroundColor":"#0073aa","textColor":"#ffffff"} -->
    <a class="gb-button gb-button-a3525e9a" href="#">
        <span class="gb-button-text">Primary Button</span>
    </a>
    <!-- /wp:generateblocks/button -->

    <!-- wp:generateblocks/button {"uniqueId":"1b644ac6","backgroundColor":"transparent","textColor":"#0073aa","border":"2px solid #0073aa"} -->
    <a class="gb-button gb-button-1b644ac6" href="#">
        <span class="gb-button-text">Secondary Button</span>
    </a>
    <!-- /wp:generateblocks/button -->
</div>
<!-- /wp:generateblocks/button-container -->
```

**Button Attributes:**
- `url`: Link URL
- `target`: Link target (_blank, _self)
- `rel`: Link relationship (noopener, noreferrer, nofollow)
- `backgroundColor`, `textColor`
- `backgroundColorHover`, `textColorHover`
- `paddingTop/Right/Bottom/Left`
- `borderRadius`
- `icon`: Icon HTML or class
- `iconLocation`: left, right

### Headline Block

Headings and text.

```html
<!-- wp:generateblocks/headline {"uniqueId":"8a47cb1b","element":"h2","fontSize":"32"} -->
<h2 class="gb-headline gb-headline-8a47cb1b">Headline Text</h2>
<!-- /wp:generateblocks/headline -->

<!-- With icon -->
<!-- wp:generateblocks/headline {"uniqueId":"b30bd2fa","element":"h3","icon":"<svg>...</svg>","hasIcon":true} -->
<h3 class="gb-headline gb-headline-b30bd2fa gb-headline-has-icon">
    <span class="gb-icon"><svg>...</svg></span>
    <span class="gb-headline-text">Headline with Icon</span>
</h3>
<!-- /wp:generateblocks/headline -->
```

**Headline Attributes:**
- `element`: h1, h2, h3, h4, h5, h6, p, div
- `fontSize`, `fontSizeTablet`, `fontSizeMobile`
- `fontWeight`: 100-900
- `textTransform`: uppercase, lowercase, capitalize
- `letterSpacing`: Letter spacing value
- `lineHeight`: Line height value
- `textColor`
- `highlightTextColor`: Color for highlighted text

### Image Block

Enhanced image handling.

```html
<!-- wp:generateblocks/image {"uniqueId":"e10dac8c","mediaId":123,"mediaUrl":"image.jpg"} -->
<figure class="gb-image gb-image-e10dac8c">
    <img src="image.jpg" alt="Alt text" />
</figure>
<!-- /wp:generateblocks/image -->

<!-- With link and caption -->
<!-- wp:generateblocks/image {"uniqueId":"11a34dda","mediaId":456,"href":"https://example.com"} -->
<figure class="gb-image gb-image-11a34dda">
    <a href="https://example.com">
        <img src="image.jpg" alt="Alt text" />
    </a>
    <figcaption>Image caption</figcaption>
</figure>
<!-- /wp:generateblocks/image -->
```

## GenerateBlocks Pro Features

### Query Loop Block

Dynamic content loops.

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"303ad9f8","postType":"post","postsPerPage":6} -->
<!-- wp:generateblocks/loop-item {"uniqueId":"03851512"} -->
<div class="gb-loop-item">
    <!-- Dynamic content blocks -->
</div>
<!-- /wp:generateblocks/loop-item -->
<!-- /wp:generateblocks/query-loop -->
```

**Query Attributes:**
- `postType`: post, page, custom_type
- `postsPerPage`: Number of posts
- `offset`: Skip posts
- `orderBy`: date, title, menu_order, rand
- `order`: DESC, ASC
- `taxQuery`: Taxonomy filtering
- `stickyPosts`: include, exclude, only
- `author`: Author ID
- `excludeCurrent`: Exclude current post

### Dynamic Data

Insert dynamic content anywhere.

**Available Dynamic Tags:**

```
// Post Data
{{post_title}}
{{post_excerpt}}
{{post_content}}
{{post_date}}
{{post_modified_date}}
{{post_author}}
{{post_id}}
{{post_url}}

// Featured Image
{{featured_image}}
{{featured_image_url}}

// Terms/Taxonomies
{{post_terms source="category"}}
{{post_terms source="post_tag" separator=", "}}

// Custom Fields / ACF
{{post_meta meta_key="field_name"}}
{{acf field="field_name"}}

// Author Data
{{author_name}}
{{author_email}}
{{author_avatar}}
{{author_meta meta_key="description"}}

// Comments
{{comments_count}}
{{comments_url}}

// Site Data
{{site_title}}
{{site_tagline}}
{{home_url}}
{{current_year}}

// User Data
{{user_name}}
{{user_email}}
{{user_meta meta_key="key"}}
```

**Dynamic Data in Blocks:**

```html
<!-- Dynamic headline -->
<!-- wp:generateblocks/headline {"uniqueId":"7837c26c","element":"h1","dynamicContentType":"post-title"} -->
<h1 class="gb-headline gb-headline-7837c26c">{{post_title}}</h1>
<!-- /wp:generateblocks/headline -->

<!-- Dynamic image -->
<!-- wp:generateblocks/image {"uniqueId":"b87c2145","useDynamicData":true,"dynamicContentType":"featured-image"} -->
<figure class="gb-image gb-image-b87c2145">
    {{featured_image}}
</figure>
<!-- /wp:generateblocks/image -->

<!-- Dynamic link -->
<!-- wp:generateblocks/button {"uniqueId":"cf4199cd","dynamicLinkType":"post-url"} -->
<a class="gb-button gb-button-cf4199cd" href="{{post_url}}">Read More</a>
<!-- /wp:generateblocks/button -->
```

### Effects (GB Pro)

Add visual effects to blocks.

```json
{
    "effects": {
        "opacity": "0.8",
        "opacityHover": "1",
        "transform": "translateY(0px)",
        "transformHover": "translateY(-5px)",
        "transition": "all 0.3s ease",
        "boxShadow": "0 4px 6px rgba(0,0,0,0.1)",
        "boxShadowHover": "0 8px 25px rgba(0,0,0,0.15)",
        "filter": "grayscale(0%)",
        "filterHover": "grayscale(100%)"
    }
}
```

### Advanced Backgrounds (GB Pro)

Multiple background layers.

```json
{
    "backgrounds": [
        {
            "type": "gradient",
            "gradient": "linear-gradient(135deg, #667eea 0%, #764ba2 100%)"
        },
        {
            "type": "image",
            "url": "pattern.png",
            "size": "100px",
            "repeat": "repeat"
        }
    ]
}
```

## Local & Global Styles

### Local Styles

Applied to individual block instance.

```html
<!-- wp:generateblocks/container {"uniqueId":"9eb0e1da","useLocalStyle":true} -->
<div class="gb-container gb-container-9eb0e1da">
    <!-- Styles apply only to this block -->
</div>
<!-- /wp:generateblocks/container -->
```

### Global Styles

Reusable styles across blocks.

1. **Create Global Style:**
   - Go to GenerateBlocks > Global Styles
   - Add new style set
   - Configure settings

2. **Apply to Block:**
   - Select block in editor
   - Open "Global Styles" panel
   - Select style to apply

```html
<!-- wp:generateblocks/button {"uniqueId":"d49b460e","globalStyleId":"primary-button"} -->
<a class="gb-button gb-button-d49b460e gb-button-global-primary-button" href="#">
    Button Text
</a>
<!-- /wp:generateblocks/button -->
```

## Pattern Library

### Register Custom Patterns

```php
add_action( 'init', 'my_register_gb_patterns' );
function my_register_gb_patterns() {
    register_block_pattern(
        'my-theme/hero-section',
        array(
            'title'       => __( 'Hero Section', 'textdomain' ),
            'description' => __( 'Full-width hero with text and CTA.', 'textdomain' ),
            'categories'  => array( 'generateblocks', 'featured' ),
            'content'     => '<!-- wp:generateblocks/container {"uniqueId":"c7982085","align":"full","paddingTop":"100","paddingBottom":"100","backgroundColor":"#1a1a1a"} -->
<div class="gb-container gb-container-c7982085 alignfull">
    <!-- wp:generateblocks/container {"uniqueId":"0c1aa271","width":"800","widthMobile":"100","marginLeft":"auto","marginRight":"auto","textAlign":"center"} -->
    <div class="gb-container gb-container-0c1aa271">
        <!-- wp:generateblocks/headline {"uniqueId":"ab651c71","element":"h1","textColor":"#ffffff","fontSize":"48"} -->
        <h1 class="gb-headline gb-headline-ab651c71">Welcome to Our Site</h1>
        <!-- /wp:generateblocks/headline -->
        <!-- wp:generateblocks/headline {"uniqueId":"134435af","element":"p","textColor":"#cccccc","fontSize":"18"} -->
        <p class="gb-headline gb-headline-134435af">Your tagline goes here</p>
        <!-- /wp:generateblocks/headline -->
        <!-- wp:generateblocks/button-container {"uniqueId":"42c02b64"} -->
        <div class="gb-button-wrapper">
            <!-- wp:generateblocks/button {"uniqueId":"85f3439b","backgroundColor":"#0073aa","textColor":"#ffffff"} -->
            <a class="gb-button gb-button-85f3439b" href="#">Get Started</a>
            <!-- /wp:generateblocks/button -->
        </div>
        <!-- /wp:generateblocks/button-container -->
    </div>
    <!-- /wp:generateblocks/container -->
</div>
<!-- /wp:generateblocks/container -->',
        )
    );
}
```

### Pattern Categories

```php
add_action( 'init', 'my_register_pattern_categories' );
function my_register_pattern_categories() {
    register_block_pattern_category(
        'my-theme-layouts',
        array( 'label' => __( 'My Theme Layouts', 'textdomain' ) )
    );
}
```

## CSS Customization

### Targeting GB Blocks

```css
/* Container */
.gb-container {
    /* Base styles */
}

.gb-container-5b449fe0 {
    /* Specific container by uniqueId */
}

/* Grid */
.gb-grid-wrapper {
    /* Grid wrapper */
}

.gb-grid-column {
    /* Grid columns */
}

/* Buttons */
.gb-button {
    /* Base button */
}

.gb-button-wrapper {
    /* Button group */
}

/* Headline */
.gb-headline {
    /* Base headline */
}

.gb-headline-has-icon {
    /* Headline with icon */
}

/* Image */
.gb-image {
    /* Image block */
}

.gb-image img {
    /* Image element */
}
```

### Responsive Utilities

```css
/* GB generates these for responsive settings */
@media (max-width: 1024px) {
    .gb-container-4656bc5b {
        /* Tablet styles */
    }
}

@media (max-width: 768px) {
    .gb-container-4656bc5b {
        /* Mobile styles */
    }
}
```

## PHP Hooks & Filters

### Block Output Filters

```php
// Filter container block output
add_filter( 'generateblocks_container_tagname', 'my_container_tag', 10, 2 );
function my_container_tag( $tagname, $attributes ) {
    if ( isset( $attributes['className'] ) && strpos( $attributes['className'], 'my-section' ) !== false ) {
        return 'section';
    }
    return $tagname;
}

// Filter button output
add_filter( 'generateblocks_button_output', 'my_button_output', 10, 3 );
function my_button_output( $output, $attributes, $block ) {
    // Modify button HTML
    return $output;
}

// Filter headline output
add_filter( 'generateblocks_headline_output', 'my_headline_output', 10, 3 );
function my_headline_output( $output, $attributes, $block ) {
    // Modify headline HTML
    return $output;
}
```

### Asset Loading

```php
// Conditionally load GB assets
add_filter( 'generateblocks_enqueue_css', 'my_conditional_gb_css' );
function my_conditional_gb_css( $enqueue ) {
    if ( is_admin() ) {
        return true;
    }

    // Only load on specific pages
    if ( is_page( array( 'home', 'about', 'contact' ) ) ) {
        return true;
    }

    return $enqueue;
}
```

### Dynamic Data Hooks

```php
// Add custom dynamic data source
add_filter( 'generateblocks_dynamic_content_output', 'my_dynamic_content', 10, 3 );
function my_dynamic_content( $output, $content_type, $attributes ) {
    if ( 'my-custom-data' === $content_type ) {
        return get_my_custom_data();
    }
    return $output;
}

// Filter post meta output
add_filter( 'generateblocks_dynamic_post_meta', 'my_post_meta_output', 10, 3 );
function my_post_meta_output( $output, $meta_key, $attributes ) {
    if ( 'my_field' === $meta_key ) {
        return esc_html( $output ) . ' custom suffix';
    }
    return $output;
}
```

## References

For detailed information:
- **Block attributes reference**: See [references/block-attributes.md](references/block-attributes.md)
- **Query Loop patterns**: See [references/query-patterns.md](references/query-patterns.md)

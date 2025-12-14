# GeneratePress Premium Elements Guide

GP Premium Elements allow you to add content, modify layouts, and customize headers/blocks without coding.

## Element Types

### 1. Hook Element

Add HTML/PHP content to any GP hook location.

**Settings:**
- **Content**: HTML/PHP code
- **Execute PHP**: Enable PHP execution
- **Hook**: Select GP hook location
- **Priority**: Execution order (default: 10)
- **Display Rules**: Where to show

**Example - Top Bar:**
```html
<div class="top-bar">
    <div class="grid-container">
        <span class="top-bar-phone">
            <svg>...</svg> 123-456-7890
        </span>
        <span class="top-bar-email">
            <svg>...</svg> info@example.com
        </span>
    </div>
</div>
```

**Example - CTA with PHP:**
```php
<?php if ( is_user_logged_in() ) : ?>
    <div class="member-cta">
        <p>Welcome back, <?php echo esc_html( wp_get_current_user()->display_name ); ?>!</p>
    </div>
<?php else : ?>
    <div class="guest-cta">
        <p>Join our community today!</p>
        <a href="<?php echo esc_url( wp_registration_url() ); ?>">Sign Up</a>
    </div>
<?php endif; ?>
```

### 2. Layout Element

Control page structure and components.

**Layout Options:**
- Sidebar Layout: Left, Right, Both, None
- Content Container: Full Width, Contained
- Inner Content Container: Full Width, Contained

**Disable Elements:**
- Header
- Navigation
- Featured Image
- Content Title
- Footer

**Content Settings:**
- Padding (Top, Right, Bottom, Left)
- Content separators

**Example Use Cases:**
- Full-width landing pages
- Sidebar-free product pages
- Custom blog layouts

### 3. Header Element

Replace the entire header with custom design.

**Available Tags:**
- `{{logo}}` - Site logo
- `{{site-title}}` - Site name
- `{{site-tagline}}` - Site description
- `{{primary_navigation}}` - Primary menu
- `{{secondary_navigation}}` - Secondary menu (if enabled)
- `{{navigation_search}}` - Search in navigation
- `{{cart}}` - WooCommerce cart icon

**Example - Centered Header:**
```html
<header class="custom-header" itemtype="https://schema.org/WPHeader" itemscope>
    <div class="custom-header-inner grid-container">
        <div class="header-row header-top">
            <div class="site-branding">
                {{logo}}
            </div>
        </div>
        <div class="header-row header-bottom">
            <nav class="main-navigation">
                {{primary_navigation}}
            </nav>
        </div>
    </div>
</header>
```

**Example - Multi-row Header:**
```html
<header class="custom-header">
    <div class="header-top-row">
        <div class="grid-container">
            <span class="header-contact">Call: 123-456-7890</span>
            <div class="header-social">
                <a href="#">Facebook</a>
                <a href="#">Twitter</a>
            </div>
        </div>
    </div>
    <div class="header-main-row">
        <div class="grid-container">
            <div class="header-logo">
                {{logo}}
            </div>
            <div class="header-nav">
                {{primary_navigation}}
            </div>
            <div class="header-actions">
                {{navigation_search}}
                {{cart}}
            </div>
        </div>
    </div>
</header>
```

### 4. Block Element

Add Gutenberg blocks to hook locations.

**Settings:**
- Block content via Block Editor
- Hook location selection
- Display rules

**Benefits:**
- Visual editing
- Full block library access
- GP Blocks integration
- Dynamic blocks support

## Display Rules

### Location Rules

**Entire Site:**
- All pages
- Front page
- Blog
- Archives
- Search results
- 404 page

**Posts:**
- All posts
- Specific post
- Posts in category/tag
- Post format

**Pages:**
- All pages
- Specific page
- Child of specific page
- Page template

**Archives:**
- Author archive
- Date archive
- Category archive
- Tag archive
- Custom taxonomy

**Custom Post Types:**
- All [CPT]
- Single [CPT]
- [CPT] Archive
- [CPT] in taxonomy

### User Rules

- Logged in users
- Logged out users
- User role (Admin, Editor, etc.)
- Specific user

### Device Rules (GP Premium 2.0+)

- Desktop
- Tablet
- Mobile

## Dynamic Data Tags

Use in Hook and Header Elements.

### Post Data
```
{{post_title}}
{{post_excerpt}}
{{post_content}}
{{post_id}}
{{post_url}}
{{post_slug}}
```

### Post Meta
```
{{post_date}}
{{post_modified_date}}
{{post_author}}
{{post_author_url}}
{{post_comments_count}}
```

### Featured Image
```
{{post_image}}
{{post_image_url}}
{{post_image_id}}
```

### Terms
```
{{post_terms.category}}
{{post_terms.post_tag}}
{{post_terms.custom_taxonomy}}
```

### Custom Fields
```
{{post_meta.field_name}}
{{custom_field.field_name}}
```

### ACF Fields (if ACF active)
```
{{acf.field_name}}
{{acf.field_name.sub_field}}
```

### Site Data
```
{{site_title}}
{{site_tagline}}
{{site_url}}
{{current_year}}
```

### Author Data
```
{{author_name}}
{{author_email}}
{{author_url}}
{{author_bio}}
{{author_avatar}}
```

### Example with Dynamic Data
```html
<div class="post-hero">
    <div class="post-hero-image" style="background-image: url('{{post_image_url}}');">
        <div class="post-hero-content">
            <span class="post-category">{{post_terms.category}}</span>
            <h1>{{post_title}}</h1>
            <div class="post-meta">
                <span class="post-author">By {{post_author}}</span>
                <span class="post-date">{{post_date}}</span>
            </div>
        </div>
    </div>
</div>
```

## CSS for Elements

### Hook Element Styling

```css
/* Top bar example */
.top-bar {
    background: #23282d;
    color: #fff;
    padding: 10px 0;
    font-size: 14px;
}

.top-bar .grid-container {
    display: flex;
    justify-content: space-between;
    align-items: center;
}

.top-bar a {
    color: #fff;
}

@media (max-width: 768px) {
    .top-bar .grid-container {
        flex-direction: column;
        text-align: center;
    }
}
```

### Header Element Styling

```css
/* Custom header */
.custom-header {
    background: #fff;
    box-shadow: 0 2px 10px rgba(0,0,0,0.1);
}

.custom-header-inner {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 20px 40px;
}

.custom-header .site-branding {
    flex: 0 0 auto;
}

.custom-header .main-navigation {
    flex: 1;
    display: flex;
    justify-content: flex-end;
}

.custom-header .main-navigation .main-nav > ul {
    display: flex;
    gap: 30px;
}

.custom-header .main-navigation .main-nav > ul > li > a {
    padding: 10px 0;
    color: #23282d;
    font-weight: 500;
}
```

## Best Practices

1. **Use specific display rules** - Avoid loading elements where not needed
2. **Minimize PHP execution** - Only enable when necessary
3. **Mobile-first CSS** - Consider responsive design
4. **Cache-friendly** - Avoid user-specific content in cached elements
5. **Semantic HTML** - Use proper HTML structure in Header Elements
6. **Test display rules** - Verify elements show correctly across conditions

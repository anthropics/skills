---
name: generatepress
description: GeneratePress theme development expert for customizing and extending GeneratePress and GeneratePress Premium. Use when working with GP hooks, Elements, Layout settings, Dynamic Data, Site Library, custom CSS/PHP for GeneratePress, child theme development, or any GeneratePress-specific customization task.
---

# GeneratePress Development Guide

Expert guidance for customizing and extending GeneratePress theme.

## Core Concepts

GeneratePress is a lightweight, performance-focused WordPress theme with:
- **GP Free**: Core theme with basic customization
- **GP Premium**: Advanced modules (Elements, Site Library, etc.)

## Hook System

GeneratePress provides extensive hooks for customization.

### Header Hooks

```php
// Before header
add_action( 'generate_before_header', 'my_before_header' );
function my_before_header() {
    echo '<div class="top-bar">Top bar content</div>';
}

// Inside header
add_action( 'generate_before_header_content', 'my_before_header_content' );
add_action( 'generate_after_header_content', 'my_after_header_content' );

// Header widget area
add_action( 'generate_header', 'my_header_widget', 15 );

// After header
add_action( 'generate_after_header', 'my_after_header' );

// Site branding
add_action( 'generate_before_logo', 'my_before_logo' );
add_action( 'generate_after_logo', 'my_after_logo' );
```

### Navigation Hooks

```php
// Primary navigation
add_action( 'generate_before_primary_navigation', 'my_before_nav' );
add_action( 'generate_after_primary_navigation', 'my_after_nav' );
add_action( 'generate_inside_navigation', 'my_inside_nav' );

// Mobile menu
add_action( 'generate_inside_mobile_menu', 'my_mobile_menu_content' );
add_action( 'generate_inside_mobile_menu_bar', 'my_mobile_bar_content' );

// Secondary navigation (GP Premium)
add_action( 'generate_inside_secondary_navigation', 'my_secondary_nav' );
```

### Content Hooks

```php
// Main content wrapper
add_action( 'generate_before_main_content', 'my_before_main' );
add_action( 'generate_after_main_content', 'my_after_main' );

// Before/after loop
add_action( 'generate_before_loop', 'my_before_loop' );
add_action( 'generate_after_loop', 'my_after_loop' );

// Single entry (post/page)
add_action( 'generate_before_entry_title', 'my_before_title' );
add_action( 'generate_after_entry_title', 'my_after_title' );
add_action( 'generate_before_content', 'my_before_content' );
add_action( 'generate_after_content', 'my_after_content' );

// Archive entry
add_action( 'generate_before_archive_title', 'my_before_archive_title' );
add_action( 'generate_after_archive_title', 'my_after_archive_title' );
add_action( 'generate_after_archive_description', 'my_after_archive_desc' );

// Featured image
add_action( 'generate_before_featured_image', 'my_before_featured' );
add_action( 'generate_after_featured_image', 'my_after_featured' );
```

### Footer Hooks

```php
// Footer
add_action( 'generate_before_footer', 'my_before_footer' );
add_action( 'generate_after_footer', 'my_after_footer' );
add_action( 'generate_before_footer_content', 'my_before_footer_content' );
add_action( 'generate_after_footer_content', 'my_after_footer_content' );

// Footer widgets
add_action( 'generate_before_footer_widgets', 'my_before_footer_widgets' );
add_action( 'generate_after_footer_widgets', 'my_after_footer_widgets' );

// Footer bar
add_action( 'generate_before_footer_bar', 'my_before_footer_bar' );
add_action( 'generate_after_footer_bar', 'my_after_footer_bar' );
add_action( 'generate_inside_footer_bar', 'my_inside_footer_bar' );
```

### Sidebar Hooks

```php
add_action( 'generate_before_right_sidebar_content', 'my_before_sidebar' );
add_action( 'generate_after_right_sidebar_content', 'my_after_sidebar' );
add_action( 'generate_before_left_sidebar_content', 'my_before_left_sidebar' );
add_action( 'generate_after_left_sidebar_content', 'my_after_left_sidebar' );
```

## Filters

### Layout Filters

```php
// Sidebar layout
add_filter( 'generate_sidebar_layout', 'my_sidebar_layout' );
function my_sidebar_layout( $layout ) {
    if ( is_singular( 'product' ) ) {
        return 'no-sidebar';
    }
    return $layout;
}

// Content width
add_filter( 'generate_content_width', 'my_content_width' );
function my_content_width( $width ) {
    if ( is_page_template( 'full-width.php' ) ) {
        return 1600;
    }
    return $width;
}

// Container classes
add_filter( 'generate_inside_container_class', 'my_container_class' );
function my_container_class( $classes ) {
    $classes[] = 'custom-container';
    return $classes;
}
```

### Navigation Filters

```php
// Mobile menu label
add_filter( 'generate_mobile_menu_label', 'my_mobile_label' );
function my_mobile_label() {
    return __( 'Menu', 'textdomain' );
}

// Menu toggle attributes
add_filter( 'generate_menu_toggle_attributes', 'my_toggle_attrs' );
function my_toggle_attrs( $attrs ) {
    $attrs['aria-expanded'] = 'false';
    return $attrs;
}

// Navigation item output
add_filter( 'generate_nav_menu_item_output', 'my_nav_item', 10, 4 );
function my_nav_item( $output, $item, $depth, $args ) {
    // Modify menu item output
    return $output;
}
```

### Post Meta Filters

```php
// Post meta items
add_filter( 'generate_post_meta_items', 'my_post_meta' );
function my_post_meta( $items ) {
    // Default: ['date', 'author', 'categories', 'comments', 'tags']
    return array( 'date', 'author', 'categories' );
}

// Date format
add_filter( 'generate_post_date_output', 'my_date_format', 10, 2 );
function my_date_format( $output, $time_string ) {
    return sprintf(
        '<span class="posted-on">%s</span>',
        $time_string
    );
}

// Author output
add_filter( 'generate_post_author_output', 'my_author_output' );
function my_author_output( $output ) {
    return sprintf(
        '<span class="byline">By %s</span>',
        get_the_author()
    );
}
```

### Typography & Styling Filters

```php
// Font display
add_filter( 'generate_google_font_display', 'my_font_display' );
function my_font_display() {
    return 'swap';
}

// Body classes
add_filter( 'body_class', 'my_body_classes' );
function my_body_classes( $classes ) {
    if ( generate_get_option( 'nav_layout_setting' ) === 'nav-float-right' ) {
        $classes[] = 'nav-aligned-right';
    }
    return $classes;
}
```

### Excerpt Filters

```php
// Excerpt length
add_filter( 'generate_excerpt_length', 'my_excerpt_length' );
function my_excerpt_length( $length ) {
    return 30;
}

// Read more text
add_filter( 'generate_read_more_text', 'my_read_more' );
function my_read_more() {
    return __( 'Continue reading', 'textdomain' );
}
```

## GP Premium Elements

### Hook Element

Create PHP/HTML content attached to hooks:

```php
// In GP Premium > Elements > Hook
// Display Rules: Entire Site
// Hook: generate_before_footer
// Execute PHP: Enabled

<div class="cta-banner">
    <h3><?php esc_html_e( 'Subscribe Now', 'textdomain' ); ?></h3>
    <?php echo do_shortcode( '[contact-form-7 id="123"]' ); ?>
</div>
```

### Layout Element

Control layout for specific pages:

- **Sidebar Layout**: No Sidebar, Left, Right, Both
- **Content Container**: Full Width, Contained
- **Header/Footer**: Enable/Disable
- **Sticky Navigation**: Enable/Disable
- **Content Padding**: Custom values

### Header Element

Custom header with full control:

```html
<!-- GP Header Element - Custom Header -->
<header class="custom-header" itemtype="https://schema.org/WPHeader" itemscope>
    <div class="inside-header grid-container">
        <div class="header-logo">
            {{logo}}
        </div>
        <nav class="header-nav">
            {{primary_navigation}}
        </nav>
    </div>
</header>
```

### Block Element

Add Gutenberg blocks to any hook location.

## Dynamic Data (GP Premium)

```php
// In Elements or any GP Premium feature

// Post/Page title
{{post_title}}

// Custom field
{{post_meta.field_name}}

// ACF field
{{acf.field_name}}

// Featured image
{{post_image}}
{{post_image_url}}

// Author
{{post_author}}
{{post_author_url}}

// Terms
{{post_terms.category}}
{{post_terms.post_tag}}

// Date
{{post_date}}
{{post_modified_date}}

// Excerpt
{{post_excerpt}}

// Custom
{{custom_field.meta_key}}

// Site data
{{site_title}}
{{site_tagline}}
{{site_url}}

// Current year
{{current_year}}
```

## Customizer Options API

```php
// Get GeneratePress option
$option = generate_get_option( 'option_name' );

// Common options
generate_get_option( 'container_width' );        // Default: 1200
generate_get_option( 'header_layout_setting' );  // Default: 'fluid-header'
generate_get_option( 'nav_layout_setting' );     // Default: 'fluid-nav'
generate_get_option( 'content_layout_setting' ); // Default: 'separate-containers'
generate_get_option( 'sidebar_layout' );         // Default: 'right-sidebar'

// Colors
generate_get_option( 'background_color' );
generate_get_option( 'text_color' );
generate_get_option( 'link_color' );
generate_get_option( 'link_color_hover' );

// Typography
generate_get_option( 'font_body' );
generate_get_option( 'body_font_size' );
generate_get_option( 'font_heading_1' );
generate_get_option( 'heading_1_font_size' );

// Filter default options
add_filter( 'generate_option_defaults', 'my_option_defaults' );
function my_option_defaults( $defaults ) {
    $defaults['container_width'] = 1400;
    $defaults['sidebar_layout'] = 'no-sidebar';
    return $defaults;
}
```

## Child Theme Setup

### style.css

```css
/*
Theme Name:     GeneratePress Child
Theme URI:      https://example.com
Description:    GeneratePress Child Theme
Author:         Your Name
Author URI:     https://example.com
Template:       generatepress
Version:        1.0.0
License:        GNU General Public License v2 or later
License URI:    http://www.gnu.org/licenses/gpl-2.0.html
Text Domain:    generatepress-child
*/
```

### functions.php

```php
<?php
defined( 'ABSPATH' ) || exit;

/**
 * Enqueue parent and child theme styles.
 */
add_action( 'wp_enqueue_scripts', 'gp_child_enqueue_styles', 50 );
function gp_child_enqueue_styles() {
    // Parent style is already enqueued by GeneratePress

    // Enqueue child theme style
    wp_enqueue_style(
        'gp-child-style',
        get_stylesheet_directory_uri() . '/style.css',
        array( 'generate-style' ),
        filemtime( get_stylesheet_directory() . '/style.css' )
    );
}

/**
 * Add custom PHP functionality below.
 */
```

## Custom CSS Best Practices

```css
/* Use GP's CSS variables for consistency */
:root {
    --gp-primary-color: #0073aa;
    --gp-secondary-color: #23282d;
}

/* Target specific GP containers */
.site-header {
    background: var(--gp-primary-color);
}

.inside-header {
    padding: 20px;
}

/* Navigation styling */
.main-navigation {
    background: transparent;
}

.main-navigation .main-nav ul li a {
    padding: 15px 20px;
    color: var(--gp-secondary-color);
}

/* Content containers */
.separate-containers .inside-article {
    padding: 40px;
}

.one-container .site-content {
    padding: 40px;
}

/* Sidebar */
.sidebar .inside-right-sidebar,
.sidebar .inside-left-sidebar {
    padding: 40px;
}

/* Footer */
.site-footer {
    background: var(--gp-secondary-color);
    color: #fff;
}

/* Responsive (GP breakpoints) */
@media (max-width: 768px) {
    .inside-header {
        padding: 15px;
    }
}
```

## Performance Optimization

```php
// Disable unused features
add_action( 'after_setup_theme', 'gp_child_optimize' );
function gp_child_optimize() {
    // Remove post image from archives
    remove_action( 'generate_after_entry_header', 'generate_post_image' );

    // Remove entry meta from specific post types
    add_filter( 'generate_post_meta_items', function( $items ) {
        if ( is_singular( 'custom_post_type' ) ) {
            return array();
        }
        return $items;
    } );
}

// Disable GP Premium modules
add_filter( 'generate_premium_modules', 'gp_disable_modules' );
function gp_disable_modules( $modules ) {
    // Disable specific modules
    unset( $modules['generate_package_copyright'] );
    return $modules;
}
```

## References

For detailed information:
- **All hooks reference**: See [references/hooks-list.md](references/hooks-list.md)
- **Elements guide**: See [references/elements-guide.md](references/elements-guide.md)

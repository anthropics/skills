# WordPress Theme Development

## Theme Structure

```
theme-name/
├── style.css              # Theme header, main styles
├── functions.php          # Theme functions
├── index.php              # Fallback template
├── front-page.php         # Static front page
├── home.php               # Blog posts page
├── single.php             # Single post
├── single-{post-type}.php # Custom post type single
├── page.php               # Single page
├── page-{slug}.php        # Specific page template
├── archive.php            # Archive pages
├── archive-{post-type}.php# CPT archive
├── category.php           # Category archive
├── tag.php                # Tag archive
├── taxonomy-{taxonomy}.php# Custom taxonomy
├── author.php             # Author archive
├── search.php             # Search results
├── 404.php                # Not found page
├── header.php             # Header template part
├── footer.php             # Footer template part
├── sidebar.php            # Sidebar template part
├── comments.php           # Comments template
├── screenshot.png         # Theme screenshot (1200x900)
├── template-parts/        # Reusable template parts
│   ├── content.php
│   ├── content-page.php
│   └── content-none.php
├── assets/
│   ├── css/
│   ├── js/
│   └── images/
├── inc/                   # PHP includes
│   ├── customizer.php
│   ├── template-tags.php
│   └── template-functions.php
└── languages/             # Translation files
```

## style.css Header

```css
/*
Theme Name:        Theme Name
Theme URI:         https://example.com/theme
Author:            Author Name
Author URI:        https://example.com
Description:       Theme description here.
Version:           1.0.0
Requires at least: 6.0
Tested up to:      6.4
Requires PHP:      7.4
License:           GNU General Public License v2 or later
License URI:       http://www.gnu.org/licenses/gpl-2.0.html
Text Domain:       theme-name
Tags:              blog, custom-background, custom-logo, custom-menu
*/
```

## functions.php Setup

```php
<?php
defined( 'ABSPATH' ) || exit;

define( 'THEME_VERSION', '1.0.0' );
define( 'THEME_DIR', get_template_directory() );
define( 'THEME_URI', get_template_directory_uri() );

/**
 * Theme setup.
 */
function theme_name_setup() {
    // Make theme available for translation
    load_theme_textdomain( 'theme-name', THEME_DIR . '/languages' );

    // Add theme support
    add_theme_support( 'automatic-feed-links' );
    add_theme_support( 'title-tag' );
    add_theme_support( 'post-thumbnails' );
    add_theme_support( 'html5', array(
        'search-form',
        'comment-form',
        'comment-list',
        'gallery',
        'caption',
        'style',
        'script',
    ) );
    add_theme_support( 'customize-selective-refresh-widgets' );
    add_theme_support( 'responsive-embeds' );
    add_theme_support( 'wp-block-styles' );
    add_theme_support( 'align-wide' );
    add_theme_support( 'editor-styles' );
    add_editor_style( 'assets/css/editor-style.css' );

    // Custom logo
    add_theme_support( 'custom-logo', array(
        'height'      => 100,
        'width'       => 400,
        'flex-height' => true,
        'flex-width'  => true,
    ) );

    // Custom background
    add_theme_support( 'custom-background', array(
        'default-color' => 'ffffff',
    ) );

    // Custom header
    add_theme_support( 'custom-header', array(
        'width'         => 1920,
        'height'        => 600,
        'flex-width'    => true,
        'flex-height'   => true,
        'header-text'   => true,
    ) );

    // Image sizes
    add_image_size( 'theme-featured', 1200, 630, true );
    add_image_size( 'theme-thumbnail', 400, 300, true );

    // Register navigation menus
    register_nav_menus( array(
        'primary' => __( 'Primary Menu', 'theme-name' ),
        'footer'  => __( 'Footer Menu', 'theme-name' ),
        'social'  => __( 'Social Links', 'theme-name' ),
    ) );
}
add_action( 'after_setup_theme', 'theme_name_setup' );

/**
 * Register widget areas.
 */
function theme_name_widgets_init() {
    register_sidebar( array(
        'name'          => __( 'Sidebar', 'theme-name' ),
        'id'            => 'sidebar-1',
        'description'   => __( 'Main sidebar area.', 'theme-name' ),
        'before_widget' => '<section id="%1$s" class="widget %2$s">',
        'after_widget'  => '</section>',
        'before_title'  => '<h2 class="widget-title">',
        'after_title'   => '</h2>',
    ) );

    register_sidebar( array(
        'name'          => __( 'Footer', 'theme-name' ),
        'id'            => 'footer-1',
        'before_widget' => '<div id="%1$s" class="widget %2$s">',
        'after_widget'  => '</div>',
        'before_title'  => '<h3 class="widget-title">',
        'after_title'   => '</h3>',
    ) );
}
add_action( 'widgets_init', 'theme_name_widgets_init' );

/**
 * Enqueue scripts and styles.
 */
function theme_name_scripts() {
    // Main stylesheet
    wp_enqueue_style(
        'theme-name-style',
        get_stylesheet_uri(),
        array(),
        THEME_VERSION
    );

    // Additional styles
    wp_enqueue_style(
        'theme-name-main',
        THEME_URI . '/assets/css/main.css',
        array(),
        THEME_VERSION
    );

    // Navigation script
    wp_enqueue_script(
        'theme-name-navigation',
        THEME_URI . '/assets/js/navigation.js',
        array(),
        THEME_VERSION,
        true
    );

    // Main script
    wp_enqueue_script(
        'theme-name-script',
        THEME_URI . '/assets/js/main.js',
        array( 'jquery' ),
        THEME_VERSION,
        true
    );

    // Comment reply script
    if ( is_singular() && comments_open() && get_option( 'thread_comments' ) ) {
        wp_enqueue_script( 'comment-reply' );
    }

    // Pass data to JS
    wp_localize_script( 'theme-name-script', 'themeNameData', array(
        'ajaxUrl' => admin_url( 'admin-ajax.php' ),
        'nonce'   => wp_create_nonce( 'theme_name_nonce' ),
    ) );
}
add_action( 'wp_enqueue_scripts', 'theme_name_scripts' );
```

## Template Hierarchy

WordPress uses this hierarchy to find templates:

### Single Post
1. `single-{post-type}-{slug}.php`
2. `single-{post-type}.php`
3. `single.php`
4. `singular.php`
5. `index.php`

### Page
1. `{custom-template}.php`
2. `page-{slug}.php`
3. `page-{id}.php`
4. `page.php`
5. `singular.php`
6. `index.php`

### Category Archive
1. `category-{slug}.php`
2. `category-{id}.php`
3. `category.php`
4. `archive.php`
5. `index.php`

### Custom Post Type Archive
1. `archive-{post-type}.php`
2. `archive.php`
3. `index.php`

### Custom Taxonomy
1. `taxonomy-{taxonomy}-{term}.php`
2. `taxonomy-{taxonomy}.php`
3. `taxonomy.php`
4. `archive.php`
5. `index.php`

## Template Tags

```php
// Header/Footer
get_header();
get_header( 'custom' ); // header-custom.php
get_footer();
get_sidebar();

// Template parts
get_template_part( 'template-parts/content', 'page' );
get_template_part( 'template-parts/content', get_post_type() );

// The Loop
if ( have_posts() ) :
    while ( have_posts() ) :
        the_post();
        the_title( '<h1>', '</h1>' );
        the_content();
        the_excerpt();
        the_permalink();
        the_post_thumbnail( 'large' );
        the_date();
        the_author();
        the_category( ', ' );
        the_tags( 'Tags: ', ', ' );
        comments_template();
    endwhile;
    the_posts_pagination();
else :
    get_template_part( 'template-parts/content', 'none' );
endif;

// Conditional tags
is_home();
is_front_page();
is_single();
is_page();
is_archive();
is_category();
is_tag();
is_tax();
is_author();
is_search();
is_404();
is_singular();
is_page_template( 'template-full-width.php' );
```

## Navigation Menus

```php
// Display menu
wp_nav_menu( array(
    'theme_location' => 'primary',
    'menu_id'        => 'primary-menu',
    'menu_class'     => 'nav-menu',
    'container'      => 'nav',
    'container_class'=> 'main-navigation',
    'fallback_cb'    => false,
    'depth'          => 2,
) );

// Custom walker
class Theme_Name_Walker_Nav_Menu extends Walker_Nav_Menu {
    public function start_lvl( &$output, $depth = 0, $args = null ) {
        $output .= '<ul class="sub-menu depth-' . $depth . '">';
    }

    public function start_el( &$output, $item, $depth = 0, $args = null, $id = 0 ) {
        $classes = implode( ' ', $item->classes );
        $output .= '<li class="' . esc_attr( $classes ) . '">';
        $output .= '<a href="' . esc_url( $item->url ) . '">';
        $output .= esc_html( $item->title );
        $output .= '</a>';
    }
}

// Use custom walker
wp_nav_menu( array(
    'theme_location' => 'primary',
    'walker'         => new Theme_Name_Walker_Nav_Menu(),
) );
```

## Customizer API

```php
function theme_name_customize_register( $wp_customize ) {
    // Add section
    $wp_customize->add_section( 'theme_name_options', array(
        'title'    => __( 'Theme Options', 'theme-name' ),
        'priority' => 30,
    ) );

    // Add setting
    $wp_customize->add_setting( 'theme_name_accent_color', array(
        'default'           => '#0073aa',
        'sanitize_callback' => 'sanitize_hex_color',
        'transport'         => 'postMessage',
    ) );

    // Add control
    $wp_customize->add_control( new WP_Customize_Color_Control(
        $wp_customize,
        'theme_name_accent_color',
        array(
            'label'   => __( 'Accent Color', 'theme-name' ),
            'section' => 'theme_name_options',
        )
    ) );

    // Checkbox
    $wp_customize->add_setting( 'theme_name_show_author', array(
        'default'           => true,
        'sanitize_callback' => 'rest_sanitize_boolean',
    ) );

    $wp_customize->add_control( 'theme_name_show_author', array(
        'type'    => 'checkbox',
        'label'   => __( 'Show author info', 'theme-name' ),
        'section' => 'theme_name_options',
    ) );

    // Select
    $wp_customize->add_setting( 'theme_name_layout', array(
        'default'           => 'sidebar-right',
        'sanitize_callback' => 'theme_name_sanitize_layout',
    ) );

    $wp_customize->add_control( 'theme_name_layout', array(
        'type'    => 'select',
        'label'   => __( 'Layout', 'theme-name' ),
        'section' => 'theme_name_options',
        'choices' => array(
            'sidebar-right' => __( 'Sidebar Right', 'theme-name' ),
            'sidebar-left'  => __( 'Sidebar Left', 'theme-name' ),
            'no-sidebar'    => __( 'No Sidebar', 'theme-name' ),
        ),
    ) );
}
add_action( 'customize_register', 'theme_name_customize_register' );

// Sanitization callback
function theme_name_sanitize_layout( $input ) {
    $valid = array( 'sidebar-right', 'sidebar-left', 'no-sidebar' );
    return in_array( $input, $valid, true ) ? $input : 'sidebar-right';
}

// Output customizer CSS
function theme_name_customizer_css() {
    $color = get_theme_mod( 'theme_name_accent_color', '#0073aa' );
    ?>
    <style type="text/css">
        a, .accent-color { color: <?php echo esc_attr( $color ); ?>; }
        .button, .btn { background-color: <?php echo esc_attr( $color ); ?>; }
    </style>
    <?php
}
add_action( 'wp_head', 'theme_name_customizer_css' );
```

## Block Theme (Full Site Editing)

### theme.json

```json
{
    "$schema": "https://schemas.wp.org/trunk/theme.json",
    "version": 3,
    "settings": {
        "color": {
            "palette": [
                { "slug": "primary", "color": "#0073aa", "name": "Primary" },
                { "slug": "secondary", "color": "#23282d", "name": "Secondary" }
            ]
        },
        "typography": {
            "fontFamilies": [
                {
                    "fontFamily": "-apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif",
                    "slug": "system",
                    "name": "System"
                }
            ],
            "fontSizes": [
                { "slug": "small", "size": "0.875rem", "name": "Small" },
                { "slug": "medium", "size": "1rem", "name": "Medium" },
                { "slug": "large", "size": "1.5rem", "name": "Large" }
            ]
        },
        "spacing": {
            "units": ["px", "em", "rem", "%", "vw"],
            "spacingSizes": [
                { "slug": "10", "size": "0.625rem", "name": "1" },
                { "slug": "20", "size": "1.25rem", "name": "2" }
            ]
        },
        "layout": {
            "contentSize": "800px",
            "wideSize": "1200px"
        }
    },
    "styles": {
        "color": {
            "background": "var(--wp--preset--color--white)",
            "text": "var(--wp--preset--color--secondary)"
        },
        "typography": {
            "fontFamily": "var(--wp--preset--font-family--system)",
            "fontSize": "var(--wp--preset--font-size--medium)"
        },
        "elements": {
            "link": {
                "color": { "text": "var(--wp--preset--color--primary)" }
            }
        }
    },
    "templateParts": [
        { "name": "header", "area": "header" },
        { "name": "footer", "area": "footer" }
    ]
}
```

### Block Templates

```
theme-name/
├── templates/
│   ├── index.html
│   ├── single.html
│   ├── page.html
│   ├── archive.html
│   └── 404.html
├── parts/
│   ├── header.html
│   ├── footer.html
│   └── sidebar.html
└── patterns/
    └── hero.php
```

---
name: wordpress
description: WordPress development expert for creating, optimizing, and refactoring WordPress code. Use when working with WordPress themes, plugins, hooks, filters, REST API, WP-CLI, database queries, security, performance optimization, or any WordPress-related development task. Covers PHP coding standards, WordPress Coding Standards, custom post types, taxonomies, meta boxes, shortcodes, widgets, and admin customization.
---

# WordPress Development Guide

Expert guidance for WordPress development following best practices and coding standards.

## Core Principles

### WordPress Coding Standards

Follow [WordPress Coding Standards](https://developer.wordpress.org/coding-standards/):
- Use tabs for indentation (not spaces)
- Opening braces on same line for functions/classes
- Space after opening and before closing parentheses in control structures
- Use Yoda conditions: `if ( true === $variable )`
- Prefix all functions, classes, and global variables with unique prefix

### Security Best Practices

**Always sanitize, validate, and escape:**

```php
// Input sanitization
$title = sanitize_text_field( $_POST['title'] );
$email = sanitize_email( $_POST['email'] );
$html = wp_kses_post( $_POST['content'] );
$url = esc_url_raw( $_POST['url'] );

// Output escaping
echo esc_html( $title );
echo esc_attr( $attribute );
echo esc_url( $url );
echo wp_kses_post( $content );

// Database queries - ALWAYS use prepare()
$results = $wpdb->get_results(
    $wpdb->prepare(
        "SELECT * FROM {$wpdb->posts} WHERE post_author = %d AND post_status = %s",
        $author_id,
        'publish'
    )
);

// Nonce verification
wp_nonce_field( 'my_action_nonce', 'my_nonce_field' );
if ( ! wp_verify_nonce( $_POST['my_nonce_field'], 'my_action_nonce' ) ) {
    wp_die( 'Security check failed' );
}

// Capability checks
if ( ! current_user_can( 'edit_posts' ) ) {
    wp_die( 'Unauthorized access' );
}
```

### Performance Optimization

```php
// Use transients for expensive operations
$data = get_transient( 'my_cached_data' );
if ( false === $data ) {
    $data = expensive_operation();
    set_transient( 'my_cached_data', $data, HOUR_IN_SECONDS );
}

// Optimize database queries
$posts = get_posts( array(
    'post_type'      => 'post',
    'posts_per_page' => 10,
    'no_found_rows'  => true,  // Skip pagination count
    'fields'         => 'ids', // Only get IDs if that's all you need
) );

// Use object cache when available
wp_cache_set( 'my_key', $data, 'my_group', 3600 );
$cached = wp_cache_get( 'my_key', 'my_group' );
```

## Hooks System

### Actions

```php
// Register action
add_action( 'init', 'my_prefix_init_function', 10 );

// With parameters
add_action( 'save_post', 'my_prefix_save_post', 10, 3 );
function my_prefix_save_post( $post_id, $post, $update ) {
    // Your code
}

// Custom action
do_action( 'my_prefix_custom_action', $arg1, $arg2 );
```

### Filters

```php
// Register filter
add_filter( 'the_content', 'my_prefix_filter_content', 10, 1 );
function my_prefix_filter_content( $content ) {
    return $content . '<p>Additional content</p>';
}

// Custom filter
$value = apply_filters( 'my_prefix_custom_filter', $default_value, $context );
```

### Common Hook Priorities

- `1-9`: Very early execution
- `10`: Default priority
- `11-99`: After default
- `100+`: Very late execution
- `PHP_INT_MAX`: Absolute last

## Custom Post Types & Taxonomies

```php
add_action( 'init', 'my_prefix_register_post_types' );
function my_prefix_register_post_types() {
    register_post_type( 'my_prefix_product', array(
        'labels'              => array(
            'name'               => __( 'Products', 'textdomain' ),
            'singular_name'      => __( 'Product', 'textdomain' ),
            'add_new'            => __( 'Add New', 'textdomain' ),
            'add_new_item'       => __( 'Add New Product', 'textdomain' ),
            'edit_item'          => __( 'Edit Product', 'textdomain' ),
        ),
        'public'              => true,
        'has_archive'         => true,
        'supports'            => array( 'title', 'editor', 'thumbnail', 'excerpt' ),
        'show_in_rest'        => true, // Enable Gutenberg
        'menu_icon'           => 'dashicons-cart',
        'rewrite'             => array( 'slug' => 'products' ),
    ) );

    register_taxonomy( 'product_category', 'my_prefix_product', array(
        'labels'            => array(
            'name'          => __( 'Product Categories', 'textdomain' ),
            'singular_name' => __( 'Product Category', 'textdomain' ),
        ),
        'hierarchical'      => true,
        'show_in_rest'      => true,
        'rewrite'           => array( 'slug' => 'product-category' ),
    ) );
}
```

## Meta Boxes & Custom Fields

```php
add_action( 'add_meta_boxes', 'my_prefix_add_meta_boxes' );
function my_prefix_add_meta_boxes() {
    add_meta_box(
        'my_prefix_meta_box',
        __( 'Product Details', 'textdomain' ),
        'my_prefix_meta_box_callback',
        'my_prefix_product',
        'normal',
        'high'
    );
}

function my_prefix_meta_box_callback( $post ) {
    wp_nonce_field( 'my_prefix_meta_box', 'my_prefix_meta_box_nonce' );
    $price = get_post_meta( $post->ID, '_my_prefix_price', true );
    ?>
    <p>
        <label for="my_prefix_price"><?php esc_html_e( 'Price:', 'textdomain' ); ?></label>
        <input type="number" id="my_prefix_price" name="my_prefix_price"
               value="<?php echo esc_attr( $price ); ?>" step="0.01" min="0">
    </p>
    <?php
}

add_action( 'save_post_my_prefix_product', 'my_prefix_save_meta_box' );
function my_prefix_save_meta_box( $post_id ) {
    if ( ! isset( $_POST['my_prefix_meta_box_nonce'] ) ||
         ! wp_verify_nonce( $_POST['my_prefix_meta_box_nonce'], 'my_prefix_meta_box' ) ) {
        return;
    }
    if ( defined( 'DOING_AUTOSAVE' ) && DOING_AUTOSAVE ) {
        return;
    }
    if ( ! current_user_can( 'edit_post', $post_id ) ) {
        return;
    }
    if ( isset( $_POST['my_prefix_price'] ) ) {
        update_post_meta( $post_id, '_my_prefix_price',
            sanitize_text_field( $_POST['my_prefix_price'] ) );
    }
}
```

## REST API

```php
add_action( 'rest_api_init', 'my_prefix_register_rest_routes' );
function my_prefix_register_rest_routes() {
    register_rest_route( 'my-prefix/v1', '/products', array(
        'methods'             => 'GET',
        'callback'            => 'my_prefix_get_products',
        'permission_callback' => '__return_true',
        'args'                => array(
            'per_page' => array(
                'default'           => 10,
                'sanitize_callback' => 'absint',
            ),
        ),
    ) );

    register_rest_route( 'my-prefix/v1', '/products/(?P<id>\d+)', array(
        'methods'             => 'GET',
        'callback'            => 'my_prefix_get_product',
        'permission_callback' => '__return_true',
        'args'                => array(
            'id' => array(
                'validate_callback' => function( $param ) {
                    return is_numeric( $param );
                },
            ),
        ),
    ) );
}

function my_prefix_get_products( $request ) {
    $per_page = $request->get_param( 'per_page' );
    $products = get_posts( array(
        'post_type'      => 'my_prefix_product',
        'posts_per_page' => $per_page,
    ) );
    return rest_ensure_response( $products );
}
```

## AJAX Handling

```php
// Enqueue script with localization
add_action( 'wp_enqueue_scripts', 'my_prefix_enqueue_scripts' );
function my_prefix_enqueue_scripts() {
    wp_enqueue_script( 'my-prefix-ajax',
        plugin_dir_url( __FILE__ ) . 'js/ajax.js',
        array( 'jquery' ),
        '1.0.0',
        true
    );
    wp_localize_script( 'my-prefix-ajax', 'myPrefixAjax', array(
        'ajaxurl' => admin_url( 'admin-ajax.php' ),
        'nonce'   => wp_create_nonce( 'my_prefix_ajax_nonce' ),
    ) );
}

// AJAX handlers
add_action( 'wp_ajax_my_prefix_action', 'my_prefix_ajax_handler' );
add_action( 'wp_ajax_nopriv_my_prefix_action', 'my_prefix_ajax_handler' );
function my_prefix_ajax_handler() {
    check_ajax_referer( 'my_prefix_ajax_nonce', 'nonce' );

    $data = sanitize_text_field( $_POST['data'] ?? '' );

    // Process request
    $result = array( 'success' => true, 'data' => $data );

    wp_send_json_success( $result );
}
```

## Enqueuing Assets

```php
add_action( 'wp_enqueue_scripts', 'my_prefix_enqueue_assets' );
function my_prefix_enqueue_assets() {
    // Styles
    wp_enqueue_style(
        'my-prefix-style',
        get_template_directory_uri() . '/assets/css/style.css',
        array(),
        filemtime( get_template_directory() . '/assets/css/style.css' )
    );

    // Scripts
    wp_enqueue_script(
        'my-prefix-script',
        get_template_directory_uri() . '/assets/js/script.js',
        array( 'jquery' ),
        filemtime( get_template_directory() . '/assets/js/script.js' ),
        true // In footer
    );

    // Conditional loading
    if ( is_singular( 'product' ) ) {
        wp_enqueue_script( 'my-prefix-product-script', /* ... */ );
    }
}

// Admin assets
add_action( 'admin_enqueue_scripts', 'my_prefix_admin_assets' );
function my_prefix_admin_assets( $hook ) {
    if ( 'post.php' !== $hook && 'post-new.php' !== $hook ) {
        return;
    }
    wp_enqueue_style( 'my-prefix-admin-style', /* ... */ );
}
```

## Plugin Development Structure

```
my-plugin/
├── my-plugin.php           # Main plugin file
├── includes/
│   ├── class-my-plugin.php # Main plugin class
│   ├── class-admin.php     # Admin functionality
│   └── class-frontend.php  # Frontend functionality
├── admin/
│   ├── css/
│   └── js/
├── public/
│   ├── css/
│   └── js/
├── templates/              # Template files
├── languages/              # Translation files
└── readme.txt              # WordPress.org readme
```

### Main Plugin File Header

```php
<?php
/**
 * Plugin Name:       My Plugin
 * Plugin URI:        https://example.com/my-plugin
 * Description:       Plugin description here.
 * Version:           1.0.0
 * Requires at least: 6.0
 * Requires PHP:      7.4
 * Author:            Your Name
 * Author URI:        https://example.com
 * License:           GPL v2 or later
 * License URI:       https://www.gnu.org/licenses/gpl-2.0.html
 * Text Domain:       my-plugin
 * Domain Path:       /languages
 */

defined( 'ABSPATH' ) || exit;

define( 'MY_PLUGIN_VERSION', '1.0.0' );
define( 'MY_PLUGIN_PATH', plugin_dir_path( __FILE__ ) );
define( 'MY_PLUGIN_URL', plugin_dir_url( __FILE__ ) );
```

## WP-CLI Commands

```php
if ( defined( 'WP_CLI' ) && WP_CLI ) {
    WP_CLI::add_command( 'my-prefix', 'My_Prefix_CLI_Command' );
}

class My_Prefix_CLI_Command {
    /**
     * Generates sample data.
     *
     * ## OPTIONS
     *
     * [--count=<number>]
     * : Number of items to generate.
     * ---
     * default: 10
     * ---
     *
     * ## EXAMPLES
     *
     *     wp my-prefix generate --count=20
     */
    public function generate( $args, $assoc_args ) {
        $count = (int) ( $assoc_args['count'] ?? 10 );

        $progress = \WP_CLI\Utils\make_progress_bar( 'Generating items', $count );

        for ( $i = 0; $i < $count; $i++ ) {
            // Generate item
            $progress->tick();
        }

        $progress->finish();
        WP_CLI::success( "Generated {$count} items." );
    }
}
```

## References

For detailed information on specific topics:
- **Database operations**: See [references/database.md](references/database.md)
- **Theme development**: See [references/theme-development.md](references/theme-development.md)
- **Common hooks reference**: See [references/hooks-reference.md](references/hooks-reference.md)

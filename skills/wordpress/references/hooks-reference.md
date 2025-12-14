# WordPress Hooks Reference

## Plugin/Theme Lifecycle

### Initialization

| Hook | When | Common Use |
|------|------|------------|
| `muplugins_loaded` | After must-use plugins loaded | Very early execution |
| `plugins_loaded` | After all plugins loaded | Plugin initialization |
| `after_setup_theme` | After theme functions.php | Theme setup, features |
| `init` | After WP fully loaded | Register CPT, taxonomies |
| `wp_loaded` | After WP and plugins loaded | Late initialization |
| `admin_init` | Admin screens init | Admin-only setup |

### Request Processing

| Hook | When | Common Use |
|------|------|------------|
| `parse_request` | Request parsed | Modify query vars |
| `pre_get_posts` | Before main query | Modify queries |
| `wp` | After query setup | Access query object |
| `template_redirect` | Before template | Redirects, custom output |

### Content Rendering

| Hook | When | Common Use |
|------|------|------------|
| `wp_head` | Inside `<head>` | Meta tags, styles |
| `wp_body_open` | After `<body>` tag | Skip links, scripts |
| `wp_footer` | Before `</body>` | Footer scripts |
| `wp_enqueue_scripts` | Enqueue time | Register assets |
| `the_content` | Content filter | Modify post content |
| `the_title` | Title filter | Modify post title |

### Admin

| Hook | When | Common Use |
|------|------|------------|
| `admin_menu` | Admin menu setup | Add menu pages |
| `admin_enqueue_scripts` | Admin enqueue | Admin assets |
| `add_meta_boxes` | Meta boxes setup | Register meta boxes |
| `save_post` | Post saved | Save meta data |
| `admin_notices` | Admin notices area | Display messages |

### AJAX

| Hook | When | Common Use |
|------|------|------------|
| `wp_ajax_{action}` | Logged-in AJAX | Handle AJAX (auth) |
| `wp_ajax_nopriv_{action}` | Public AJAX | Handle AJAX (public) |

### REST API

| Hook | When | Common Use |
|------|------|------------|
| `rest_api_init` | REST API init | Register routes |
| `rest_pre_dispatch` | Before dispatch | Modify request |
| `rest_post_dispatch` | After dispatch | Modify response |

## Content Hooks

### Posts

```php
// Before/after post loop
do_action( 'loop_start', $query );
do_action( 'loop_end', $query );

// Content filters
apply_filters( 'the_content', $content );
apply_filters( 'the_title', $title, $post_id );
apply_filters( 'the_excerpt', $excerpt );

// Post save/update
do_action( 'save_post', $post_id, $post, $update );
do_action( 'save_post_{post_type}', $post_id, $post, $update );
do_action( 'wp_insert_post', $post_id, $post, $update );
do_action( 'transition_post_status', $new_status, $old_status, $post );

// Post delete
do_action( 'before_delete_post', $post_id, $post );
do_action( 'deleted_post', $post_id, $post );
do_action( 'trashed_post', $post_id );
```

### Comments

```php
do_action( 'comment_post', $comment_id, $approved, $data );
do_action( 'wp_insert_comment', $comment_id, $comment );
do_action( 'edit_comment', $comment_id, $data );
do_action( 'delete_comment', $comment_id, $comment );
apply_filters( 'comment_text', $comment_text, $comment, $args );
```

### Users

```php
do_action( 'user_register', $user_id, $userdata );
do_action( 'profile_update', $user_id, $old_user_data, $userdata );
do_action( 'delete_user', $user_id, $reassign, $user );
do_action( 'wp_login', $user_login, $user );
do_action( 'wp_logout', $user_id );
do_action( 'set_user_role', $user_id, $role, $old_roles );
```

### Terms/Taxonomies

```php
do_action( 'created_term', $term_id, $tt_id, $taxonomy, $args );
do_action( 'edited_term', $term_id, $tt_id, $taxonomy, $args );
do_action( 'delete_term', $term_id, $tt_id, $taxonomy, $deleted_term, $object_ids );
do_action( "created_{$taxonomy}", $term_id, $tt_id, $args );
```

### Options

```php
do_action( "add_option_{$option}", $option, $value );
do_action( "update_option_{$option}", $old_value, $new_value, $option );
do_action( "delete_option_{$option}", $option );
apply_filters( "pre_option_{$option}", $value, $option );
apply_filters( "option_{$option}", $value, $option );
```

### Meta

```php
do_action( "added_{$meta_type}_meta", $mid, $object_id, $meta_key, $meta_value );
do_action( "updated_{$meta_type}_meta", $meta_id, $object_id, $meta_key, $meta_value );
do_action( "deleted_{$meta_type}_meta", $meta_ids, $object_id, $meta_key, $meta_value );
apply_filters( "get_{$meta_type}_metadata", null, $object_id, $meta_key, $single, $meta_type );
```

## Template Hooks

### wp_head

```php
// Default priority hooks in wp_head
add_action( 'wp_head', 'wp_enqueue_scripts', 1 );
add_action( 'wp_head', 'wp_print_styles', 8 );
add_action( 'wp_head', 'wp_print_head_scripts', 9 );
add_action( 'wp_head', 'wp_site_icon', 99 );
```

### Body Class

```php
apply_filters( 'body_class', $classes, $class );

// Add custom body class
add_filter( 'body_class', function( $classes ) {
    if ( is_singular( 'product' ) ) {
        $classes[] = 'product-page';
    }
    return $classes;
} );
```

### Post Class

```php
apply_filters( 'post_class', $classes, $class, $post_id );
```

## Query Modification

### pre_get_posts

```php
add_action( 'pre_get_posts', function( $query ) {
    // Only modify main query on frontend
    if ( is_admin() || ! $query->is_main_query() ) {
        return;
    }

    // Modify search
    if ( $query->is_search() ) {
        $query->set( 'post_type', array( 'post', 'page', 'product' ) );
    }

    // Modify archive
    if ( $query->is_post_type_archive( 'product' ) ) {
        $query->set( 'posts_per_page', 24 );
        $query->set( 'orderby', 'title' );
        $query->set( 'order', 'ASC' );
    }
} );
```

### posts_where, posts_join, posts_orderby

```php
add_filter( 'posts_where', function( $where, $query ) {
    global $wpdb;
    if ( $query->get( 'custom_filter' ) ) {
        $where .= $wpdb->prepare(
            " AND {$wpdb->posts}.post_date > %s",
            '2024-01-01'
        );
    }
    return $where;
}, 10, 2 );
```

## Script/Style Hooks

```php
// Frontend
add_action( 'wp_enqueue_scripts', 'my_enqueue_scripts' );

// Admin
add_action( 'admin_enqueue_scripts', 'my_admin_scripts' );

// Login page
add_action( 'login_enqueue_scripts', 'my_login_scripts' );

// Block editor
add_action( 'enqueue_block_editor_assets', 'my_editor_assets' );

// Script/style filters
apply_filters( 'script_loader_tag', $tag, $handle, $src );
apply_filters( 'style_loader_tag', $tag, $handle, $href, $media );
```

## Email Hooks

```php
apply_filters( 'wp_mail', $args );
apply_filters( 'wp_mail_from', $from_email );
apply_filters( 'wp_mail_from_name', $from_name );
apply_filters( 'wp_mail_content_type', $content_type );
do_action( 'phpmailer_init', $phpmailer );
```

## Cron Hooks

```php
// Schedule event
wp_schedule_event( time(), 'hourly', 'my_hourly_event' );
wp_schedule_single_event( time() + 3600, 'my_single_event' );

// Handle event
add_action( 'my_hourly_event', 'my_hourly_function' );

// Custom schedule
add_filter( 'cron_schedules', function( $schedules ) {
    $schedules['five_minutes'] = array(
        'interval' => 300,
        'display'  => __( 'Every 5 Minutes' ),
    );
    return $schedules;
} );
```

## Security Hooks

```php
// Login
do_action( 'wp_login_failed', $username, $error );
apply_filters( 'authenticate', $user, $username, $password );
apply_filters( 'wp_authenticate_user', $user, $password );

// Capabilities
apply_filters( 'user_has_cap', $allcaps, $caps, $args, $user );
apply_filters( 'map_meta_cap', $caps, $cap, $user_id, $args );

// Nonce
apply_filters( 'nonce_life', $life );
do_action( 'check_admin_referer', $action, $result );
```

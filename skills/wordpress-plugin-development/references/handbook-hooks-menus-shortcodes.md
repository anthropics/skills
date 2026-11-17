# Hooks, Administration Menus & Shortcodes

Compiled from the WordPress Plugin Developer Handbook.

## 1. Hooks

Source: https://developer.wordpress.org/plugins/hooks/ (+ actions, filters, custom-hooks, advanced-topics)

**RULE — actions vs filters.** Actions *do* something and return nothing. Filters *modify* a value
and **MUST return** it. Need to change data flowing onward → filter; need to perform a task → action.

### Actions
`add_action( $hook, $cb, $priority = 10, $accepted_args = 1 )`. To receive >1 arg from
`do_action()`, raise `accepted_args`.
```php
function wporg_custom( $post_id, $post ) { /* ... */ }
add_action( 'save_post', 'wporg_custom', 10, 2 );
```
Fire: `do_action( $hook, $arg1, ... )`; `do_action_ref_array( $hook, $args )` for by-reference.

### Filters
`add_filter( $hook, $cb, $priority = 10, $accepted_args = 1 )` — callback MUST return.
```php
function wporg_title( $title ) { return 'The ' . $title; }
add_filter( 'the_title', 'wporg_title' );
```
Fire: `apply_filters( $hook, $value, ...$extra )` returns the value; extra args are read-only context.

### Priority & custom hooks
Lower priority runs earlier; same priority runs in registration order. Expose your own hooks for
extensibility (`do_action()` for events, `apply_filters()` for output values) and **always prefix**
hook names.
```php
do_action( 'wporg_after_settings_page_html' );
$args = apply_filters( 'wporg_post_type_args', $args );
```

### Removing hooks & advanced
`remove_action`/`remove_filter` must match the **exact same callable AND priority**, after the add.
`current_filter()` returns the executing hook; `did_action( $hook )` counts fires.

Gotchas: a filter that returns nothing wipes the value. `accepted_args` mismatch → extra args
arrive `null`. `remove_*` priority mismatch silently fails. Closures/object methods are hard to
remove. Unprefixed custom hooks collide.

## 2. Administration menus

Source: https://developer.wordpress.org/plugins/administration-menus/ (+ top-level-menus, sub-menus)

**RULE — register on `admin_menu`.** A single option page should be a **sub-menu** under an
existing parent, not a new top-level item.
```php
add_action( 'admin_menu', function () {
    add_menu_page( 'WPOrg', 'WPOrg', 'manage_options',
        'wporg', 'wporg_page_html', 'dashicons-admin-generic', 25 );
} );
```
`add_menu_page( $page_title, $menu_title, $capability, $menu_slug, $cb, $icon, $position )`.
`add_submenu_page( $parent_slug, $page_title, $menu_title, $capability, $menu_slug, $cb, $position )`.

**RULE — the page callback MUST (1) check capability and (2) escape output.**
```php
function wporg_page_html() {
    if ( ! current_user_can( 'manage_options' ) ) return;
    echo '<div class="wrap"><h1>' . esc_html( get_admin_page_title() ) . '</h1></div>';
}
```
Built-in parent slugs / wrappers: `index.php` (`add_dashboard_page`), `edit.php`
(`add_posts_page`), `upload.php` (`add_media_page`), `edit-comments.php` (`add_comments_page`),
`themes.php` (`add_theme_page`), `plugins.php` (`add_plugins_page`), `users.php`
(`add_users_page`), `tools.php` (`add_management_page`), `options-general.php`
(`add_options_page`).

Gotchas: hidden menu ≠ security boundary — the callback must still check caps. Unescaped page HTML
is XSS. Registering outside `admin_menu` doesn't work. Duplicate `$menu_slug` clobbers. Reuse the
parent slug for the landing submenu to avoid a duplicate first item.

## 3. Shortcodes

Source: https://developer.wordpress.org/plugins/shortcodes/ (+ basic, enclosing, parameters, tinymce)

**RULE — register with `add_shortcode( $tag, $cb )`; the callback MUST RETURN a string, never `echo`.**
```php
add_shortcode( 'wporg', 'wporg_shortcode' );
function wporg_shortcode( $atts = [], $content = null, $tag = '' ) {
    return $content;
}
```
Signature `( $atts, $content = null, $tag = '' )`. Related: `do_shortcode()`, `remove_shortcode()`,
`shortcode_exists()`.

### Attributes — merge defaults + sanitize/escape
```php
$atts = array_change_key_case( (array) $atts, CASE_LOWER );
$a    = shortcode_atts( [ 'title' => 'WordPress.org' ], $atts, $tag );
return '<h2>' . esc_html( $a['title'] ) . '</h2>';
```

### Enclosing & nested
`[wporg]` → `$content` null; `[wporg]...[/wporg]` → `$content` set. Run nested shortcodes:
```php
return '<div>' . do_shortcode( $content ) . '</div>';
```
TinyMCE-enhanced shortcodes render live in the visual editor (core: audio, caption, gallery,
playlist, video).

Gotchas: echoing instead of returning dumps output at the top of the post (#1 bug). Sanitize
`$atts`, escape output. Lowercase keys. Don't forget `do_shortcode($content)` for nested. Keep the
callback light (runs per occurrence). Prefix tags to avoid collisions.

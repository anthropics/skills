# Settings, Options, Metadata, Custom Post Types & Taxonomies

Compiled from the WordPress Plugin Developer Handbook.

## 1. Options API

Source: https://developer.wordpress.org/plugins/settings/options-api/

Options are key/value rows in `{$prefix}options`. Single-site: `*_option()`; multisite network-wide:
`*_site_option()`.

**RULES**
- Prefix every option name with your slug. The namespace is global.
- `add_option($name,$value,'',$autoload)` creates; fails silently if it exists.
- `get_option($name,$default)` returns value or `$default` (default `false`).
- `update_option($name,$value,$autoload)` upserts; only writes if changed.
- `delete_option($name)` removes.
- **Autoload**: autoloaded options load on every request via one query. Set `autoload=false` for
  **large** or **rarely-read** options. `update_option()` does not change autoload of an existing
  option unless passed explicitly.
- Store related settings as ONE array, not many rows.

```php
add_option( 'myplugin_settings_data', array( 'enabled' => true ), '', false );
$s = get_option( 'myplugin_settings_data', array() );
$s['enabled'] = false;
update_option( 'myplugin_settings_data', $s );
```

Gotchas: don't autoload big blobs. Unprefixed names collide. `add_option` won't overwrite.

## 2. Settings API

Source: https://developer.wordpress.org/plugins/settings/settings-api/ (+ using-settings-api)

The form POSTs to `wp-admin/options.php`, which does **capability + nonce checks for you** — so a
standard settings form needs no hand-rolled nonce/`current_user_can()`. Register on `admin_init`.

**RULES**
- `register_setting( $group, $option, $args )` whitelists the option. Use the modern `$args`:
  `type`, **`sanitize_callback` (always provide)**, `show_in_rest` (true for JS/Gutenberg access),
  `default`, `description`.
- `add_settings_section( $id, $title, $cb, $page )`.
- `add_settings_field( $id, $label, $cb, $page, $section, $args )`.
- In the form: `settings_fields( $group )` (nonce/action) + `do_settings_sections( $page )`.

```php
add_action( 'admin_init', function () {
    register_setting( 'myplugin_group', 'myplugin_settings_data', array(
        'type' => 'array', 'sanitize_callback' => 'myplugin_sanitize_settings',
        'show_in_rest' => false, 'default' => array(),
    ) );
    add_settings_section( 'myplugin_main', 'Main', '__return_false', 'myplugin_page' );
    add_settings_field( 'myplugin_enabled', 'Enabled', 'myplugin_field_html', 'myplugin_page', 'myplugin_main' );
} );
```

Gotchas: `$group` must match in `register_setting` + `settings_fields`. Missing `settings_fields()`
breaks the nonce. A missing/loose `sanitize_callback` is the main injection risk. `show_in_rest`
needed for a React/Gutenberg UI to read the option.

## 3. Post metadata

Source: https://developer.wordpress.org/plugins/metadata/ (+ managing, custom-meta-boxes)

**RULES**
- `add_post_meta($id,$key,$value,$unique)`; `update_post_meta($id,$key,$value,$prev)` (upsert);
  `get_post_meta($id,$key,$single)`; `delete_post_meta($id,$key,$value)`.
- **Underscore prefix (`_myplugin_x`)** = hidden/protected meta (excluded from the custom-fields UI).
  Also prefix with your slug.
- `register_post_meta($type,$key,$args)` with `type`, `single`, `default`, **`sanitize_callback`**,
  **`auth_callback`**, **`show_in_rest`** — preferred for Gutenberg.

```php
register_post_meta( 'post', '_myplugin_attachment_url', array(
    'type' => 'string', 'single' => true, 'show_in_rest' => true,
    'sanitize_callback' => 'esc_url_raw',
    'auth_callback' => fn( $a, $k, $pid ) => current_user_can( 'edit_post', $pid ),
) );
```

**Custom meta boxes** — `add_meta_box()` on `add_meta_boxes`; no submit button (saves with the
post). The `save_post` handler MUST guard autosave + nonce + capability + sanitization:
```php
add_action( 'save_post', function ( $post_id ) {
    if ( defined('DOING_AUTOSAVE') && DOING_AUTOSAVE ) return;
    if ( ! isset($_POST['myplugin_nonce']) || ! wp_verify_nonce($_POST['myplugin_nonce'],'myplugin_save') ) return;
    if ( ! current_user_can( 'edit_post', $post_id ) ) return;
    if ( isset($_POST['myplugin_field']) )
        update_post_meta( $post_id, '_myplugin_field', sanitize_text_field( wp_unslash( $_POST['myplugin_field'] ) ) );
} );
```

Gotchas: handbook meta-box examples omit nonce/cap/autosave/sanitize — you must add them.
`save_post` fires repeatedly. `get_post_meta(..., false)` returns an array. Block-editor fields need
`show_in_rest`.

## 4. Custom post types

Source: https://developer.wordpress.org/plugins/post-types/ (+ registering-custom-post-types)

**RULES**
- `register_post_type( $key, $args )` on `init`.
- **Key ≤ 20 chars**, lowercase, **prefixed**; never `wp_`. Generic keys collide.
- Key args: `public`, **`show_in_rest` (true → block editor + REST)**, `supports`, `has_archive`,
  `rewrite`, `capability_type`, `labels`, `menu_icon`.
- **Flush rewrite rules only on activation**, after registering — never on `init`.

```php
add_action( 'init', function () {
    register_post_type( 'myplugin_item', array(
        'public' => true, 'show_in_rest' => true, 'has_archive' => true,
        'supports' => array( 'title', 'editor' ),
        'rewrite' => array( 'slug' => 'myplugin-item' ),
        'labels' => array( 'name' => 'Items', 'singular_name' => 'Item' ),
    ) );
} );
```

Gotchas: `flush_rewrite_rules()` on `init` runs every request — activation only. Without
`show_in_rest` the type uses the classic editor and is invisible to REST/Gutenberg.

## 5. Custom taxonomies

Source: https://developer.wordpress.org/plugins/taxonomies/ (+ working-with / registering)

**RULES**
- `register_taxonomy( $taxonomy, $object_types, $args )` on `init`; register before/with the post
  types it attaches to.
- Key ≤ 32 chars, lowercase, prefixed. Args: `hierarchical`, `labels`, **`show_in_rest`**,
  `rewrite`, `public`, `show_ui`, `show_admin_column`, `query_var`.
- Associate later with `register_taxonomy_for_object_type( $taxonomy, $post_type )`.

```php
add_action( 'init', function () {
    register_taxonomy( 'myplugin_topic', array( 'post', 'myplugin_item' ), array(
        'hierarchical' => true, 'show_in_rest' => true, 'show_admin_column' => true,
        'rewrite' => array( 'slug' => 'myplugin-topic' ),
        'labels' => array( 'name' => 'Topics', 'singular_name' => 'Topic' ),
    ) );
} );
```

Gotchas: URL-affecting taxonomies need a rewrite flush on activation (not `init`). `show_in_rest`
required for the block-editor sidebar.

## Cross-cutting principles

1. Prefix everything — options, meta keys, CPT/taxonomy keys.
2. `show_in_rest` is the Gutenberg gate (settings, meta, CPT, taxonomy).
3. Never `flush_rewrite_rules()` on `init` — activation only.
4. Settings API gives nonce + capability handling free; raw meta boxes do not.

# WordPress.org Plugin Review: Common Rejection Patterns Reference

A consolidated guide for plugin authors covering hooks, path resolution, the Settings API, the uploads directory, file upload helpers, and REST API permission callbacks. Aimed at avoiding the most frequent reasons plugins are kicked back during wp.org review.

---

## 1. Hooks (Actions + Filters)

WordPress exposes two hook types. Both are registered with a callable, but they have very different contracts.

### Actions vs. filters at a glance

| Aspect | Action | Filter |
|---|---|---|
| Purpose | Run side-effect code at a chosen moment | Transform a value and return it |
| Return value | Ignored | Required — must return modified data |
| Registered with | `add_action()` | `add_filter()` |
| Fired by | `do_action()` (in core or your code) | `apply_filters()` |

### Registering an action

```php
add_action( 'init', 'myplugin_bootstrap' );

function myplugin_bootstrap() {
    // Runs once WordPress has finished loading plugins and is ready.
}
```

The signature is:

```php
add_action( string $hook_name, callable $callback, int $priority = 10, int $accepted_args = 1 );
```

A lower `$priority` runs earlier. If a hook passes multiple arguments, bump `$accepted_args` so your callback receives them:

```php
add_action( 'save_post', 'myplugin_on_save', 10, 2 );

function myplugin_on_save( $post_id, $post ) {
    // ...
}
```

### Registering a filter

```php
add_filter( 'the_title', 'myplugin_decorate_title' );

function myplugin_decorate_title( $title ) {
    return '[Featured] ' . $title; // Always return — never echo.
}
```

A filter must be free of side effects. Don't write to options, don't echo, don't redirect — just return the (possibly modified) value.

### Why core files must NOT be loaded with plain `include`

A frequent review rejection is plugins that top-level `include` core files like `wp-load.php`, `wp-admin/includes/file.php`, or `wp-blog-header.php` from the plugin's main file. This breaks because:

1. The main plugin file is loaded by WordPress itself — by the time it runs, core *is* already loading. Re-including bootstraps it twice.
2. Plugins are sometimes loaded out of band (CLI, must-use plugins, network activation). A hard `include` of an admin file fatals on the front-end.
3. Direct includes bypass the hook system, so other plugins/themes can't intercept anything.

The same anti-pattern applies inside REST route handlers, shortcode callbacks, and `the_content` filter callbacks — these should **register** themselves via hooks, then load any required core files lazily inside the callback (only when needed):

```php
// WRONG — runs on every page load, even front-end requests.
require_once ABSPATH . 'wp-admin/includes/file.php';
require_once ABSPATH . 'wp-admin/includes/media.php';

add_action( 'rest_api_init', function () {
    register_rest_route( 'myplugin/v1', '/upload', [
        'methods'             => 'POST',
        'callback'            => 'myplugin_rest_upload',
        'permission_callback' => function () { return current_user_can( 'upload_files' ); },
    ] );
} );

// RIGHT — load only inside the handler.
function myplugin_rest_upload( WP_REST_Request $request ) {
    require_once ABSPATH . 'wp-admin/includes/file.php';
    require_once ABSPATH . 'wp-admin/includes/media.php';
    // ... handle upload ...
}
```

### Never `define()` core constants

`ABSPATH`, `WP_CONTENT_DIR`, `WPINC`, `WP_PLUGIN_DIR`, and similar constants are owned by core. A plugin that defines them:

- Will fatal if the constant is already defined (which it almost always is).
- If guarded with `defined()`, will silently change core behavior on rare bootstrap paths.
- Will fail review on sight.

```php
// NEVER do this in a plugin.
if ( ! defined( 'ABSPATH' ) ) {
    define( 'ABSPATH', dirname( __FILE__ ) . '/' );
}
```

The single legitimate use of `ABSPATH` in plugin code is the front-matter direct-access guard at the top of every PHP file:

```php
<?php
defined( 'ABSPATH' ) || exit;
```

### "I need code to run only when WP is loaded"

Use a hook. Pick the earliest one whose contract matches your needs:

| Hook | When it fires | Use for |
|---|---|---|
| `plugins_loaded` | All active plugins loaded | Loading your own files, instantiating your bootstrap class |
| `init` | WP core fully initialized; user not yet resolved on front-end | Registering post types, taxonomies, shortcodes, REST routes (via `rest_api_init`), blocks |
| `wp_loaded` | Everything (plugins + theme + init) done | Final wiring that depends on theme being loaded |
| `admin_init` | Admin-only equivalent of `init` | Settings API registration, admin-only checks |

```php
// Main plugin file
add_action( 'plugins_loaded', 'myplugin_load' );

function myplugin_load() {
    require_once __DIR__ . '/includes/class-myplugin.php';
    MyPlugin::instance();
}
```

---

## 2. Determining Plugin and Content Paths

Hardcoded paths are the second-most-common rejection cause. Users can move `wp-content`, rename it, symlink it, run multisite with subdirectories, or rename your plugin's own folder.

### The four canonical functions

```php
// 1. Filesystem path to YOUR plugin's directory, with trailing slash.
$dir = plugin_dir_path( __FILE__ );
// → /var/www/html/wp-content/plugins/my-plugin/

// 2. URL to YOUR plugin's directory, with trailing slash.
$url = plugin_dir_url( __FILE__ );
// → https://example.com/wp-content/plugins/my-plugin/

// 3. URL to an asset inside YOUR plugin.
$asset = plugins_url( 'assets/logo.png', __FILE__ );
// → https://example.com/wp-content/plugins/my-plugin/assets/logo.png

// 4. __FILE__ — the magic constant resolved by PHP, used as the anchor.
```

Always pass `__FILE__` (from the main plugin file or a file that *knows* its location) as the second argument. That's how these helpers resolve symlinks and renamed `wp-content` directories correctly.

### Enqueueing assets the right way

```php
add_action( 'wp_enqueue_scripts', 'myplugin_assets' );

function myplugin_assets() {
    wp_enqueue_style(
        'myplugin',
        plugins_url( 'css/myplugin.css', MYPLUGIN_FILE ),
        [],
        MYPLUGIN_VERSION
    );
    wp_enqueue_script(
        'myplugin',
        plugins_url( 'js/myplugin.js', MYPLUGIN_FILE ),
        [ 'jquery' ],
        MYPLUGIN_VERSION,
        true
    );
}
```

### Why `WP_PLUGIN_URL . '/my-plugin'` is fragile

It looks like it should work, but it breaks under any of these conditions:

- The user renamed the plugin folder (allowed — wp.org slug isn't enforced post-install).
- `wp-content` was renamed via `WP_CONTENT_DIR` / `WP_CONTENT_URL`.
- `wp-content/plugins` is symlinked from outside the web root.
- The site runs in a multisite where `WP_PLUGIN_URL` resolves differently than expected.
- The user has `WP_PLUGIN_DIR` defined to a non-standard location.

`plugins_url( 'asset', __FILE__ )` handles all of these correctly because it resolves from your file's actual location.

### Recommended: define constants in the main plugin file

```php
<?php
/**
 * Plugin Name: My Plugin
 */
defined( 'ABSPATH' ) || exit;

define( 'MYPLUGIN_VERSION', '1.0.0' );
define( 'MYPLUGIN_FILE',    __FILE__ );
define( 'MYPLUGIN_DIR',     plugin_dir_path( __FILE__ ) ); // trailing slash
define( 'MYPLUGIN_URL',     plugin_dir_url( __FILE__ ) );  // trailing slash
define( 'MYPLUGIN_BASENAME', plugin_basename( __FILE__ ) ); // 'my-plugin/my-plugin.php'

require_once MYPLUGIN_DIR . 'includes/bootstrap.php';
```

Other files in the plugin can now use these constants and don't need their own `__FILE__` anchoring.

### `get_theme_root()` vs. `WP_CONTENT_DIR . '/themes'`

These are *not* equivalent.

- `WP_CONTENT_DIR . '/themes'` assumes the canonical layout. It will be wrong if the site uses `register_theme_directory()` to register extra theme folders, or if a multisite child has its own theme root.
- `get_theme_root()` (and `get_theme_root_uri()`) return the active theme root for the current request, honoring filters like `theme_root` and `theme_root_uri`.

```php
// WRONG — assumes one fixed theme directory.
$themes_dir = WP_CONTENT_DIR . '/themes';

// RIGHT
$themes_dir = get_theme_root();
$themes_url = get_theme_root_uri();
```

---

## 3. Settings API

Plugin settings must be stored in `wp_options` (or `wp_sitemeta` for network options), not in files inside the plugin folder. The plugin directory is wiped on upgrade, world-readable over HTTP, and not writable on many hosts.

### The workflow

```php
add_action( 'admin_init', 'myplugin_register_settings' );

function myplugin_register_settings() {

    // 1. Register the option (lives in wp_options as 'myplugin_options').
    register_setting(
        'myplugin_group',          // option group — used by settings_fields()
        'myplugin_options',        // option name in wp_options
        [
            'type'              => 'array',
            'sanitize_callback' => 'myplugin_sanitize_options',
            'default'           => [ 'enabled' => false, 'api_key' => '' ],
        ]
    );

    // 2. A visual section on the settings page.
    add_settings_section(
        'myplugin_section_main',
        __( 'Main settings', 'myplugin' ),
        'myplugin_section_main_intro',
        'myplugin'                 // page slug
    );

    // 3. Individual fields inside the section.
    add_settings_field(
        'myplugin_field_enabled',
        __( 'Enable feature', 'myplugin' ),
        'myplugin_render_enabled',
        'myplugin',                // same page slug
        'myplugin_section_main'
    );
}

function myplugin_section_main_intro() {
    echo '<p>' . esc_html__( 'Configure plugin behavior.', 'myplugin' ) . '</p>';
}

function myplugin_render_enabled() {
    $options = get_option( 'myplugin_options', [] );
    $checked = ! empty( $options['enabled'] );
    printf(
        '<input type="checkbox" name="myplugin_options[enabled]" value="1" %s>',
        checked( $checked, true, false )
    );
}
```

### Sanitize / validate callback

The sanitize callback runs every time the option is saved. It receives the raw `$_POST` value and must return the cleaned value.

```php
function myplugin_sanitize_options( $input ) {
    $output = [];
    $output['enabled'] = ! empty( $input['enabled'] );
    $output['api_key'] = isset( $input['api_key'] )
        ? sanitize_text_field( $input['api_key'] )
        : '';
    if ( $output['api_key'] !== '' && ! preg_match( '/^[A-Za-z0-9_-]{20,64}$/', $output['api_key'] ) ) {
        add_settings_error(
            'myplugin_options',
            'invalid_key',
            __( 'API key format is invalid.', 'myplugin' )
        );
        $output['api_key'] = ''; // reject the bad value
    }
    return $output;
}
```

### Rendering the form page

```php
function myplugin_render_settings_page() {
    if ( ! current_user_can( 'manage_options' ) ) {
        return;
    }
    ?>
    <div class="wrap">
        <h1><?php echo esc_html( get_admin_page_title() ); ?></h1>
        <form action="options.php" method="post">
            <?php
            settings_fields( 'myplugin_group' );   // nonce + option_page hidden inputs
            do_settings_sections( 'myplugin' );    // renders sections + fields
            submit_button();
            ?>
        </form>
    </div>
    <?php
}
```

### Why store config in `wp_options` and not in plugin files

- The plugin directory is overwritten on update — config written there is lost.
- Plugin files are served over HTTP; anything written there leaks (API keys, secrets).
- Many hosts mark `wp-content/plugins` read-only.
- Backups and migration tools expect site config in the database.

For per-site options on multisite use `get_option()`/`update_option()`. For network-wide settings use `get_site_option()`/`update_site_option()`.

---

## 4. Where to Write Files

Plugin code that needs to write to disk should *always* go through `wp_upload_dir()` — never write to your own plugin folder.

### `wp_upload_dir()` return value

`wp_upload_dir( $time = null, $create_dir = true, $refresh_cache = false )` returns an associative array:

| Key | Meaning | Example |
|---|---|---|
| `path` | Absolute filesystem path to the *current month's* uploads dir | `/var/www/wp-content/uploads/2026/05` |
| `url` | URL matching `path` | `https://example.com/wp-content/uploads/2026/05` |
| `subdir` | The relative slice (year/month or empty) | `/2026/05` |
| `basedir` | Absolute path to the uploads root (no year/month) | `/var/www/wp-content/uploads` |
| `baseurl` | URL matching `basedir` | `https://example.com/wp-content/uploads` |
| `error` | `false` on success, error string on failure | `false` |

Pass `$time` as `'YYYY/MM'` to get paths for a specific month. Year/month bucketing only happens if the site has "Organize my uploads into month- and year-based folders" enabled in Settings → Media; otherwise `path` equals `basedir` and `subdir` is empty.

### Multisite behavior

On multisite, each subsite gets its own uploads directory by default — typically `wp-content/uploads/sites/{blog_id}/`. `wp_upload_dir()` returns the *current* site's uploads, so subsite plugin code automatically writes to the right place. To target the main site explicitly, wrap the call in `switch_to_blog( get_main_site_id() )` / `restore_current_blog()`.

### Recommended pattern: a plugin-specific subdir inside uploads

```php
function myplugin_storage_dir() {
    $upload = wp_upload_dir();
    if ( ! empty( $upload['error'] ) ) {
        return new WP_Error( 'upload_dir', $upload['error'] );
    }
    $dir = trailingslashit( $upload['basedir'] ) . 'myplugin';
    if ( ! file_exists( $dir ) ) {
        wp_mkdir_p( $dir );
        // Block directory listing.
        @file_put_contents( $dir . '/index.php', "<?php\n// Silence is golden.\n" );
    }
    if ( ! is_writable( $dir ) ) {
        return new WP_Error( 'not_writable', 'Plugin storage dir is not writable.' );
    }
    return $dir;
}

function myplugin_storage_url() {
    $upload = wp_upload_dir();
    return trailingslashit( $upload['baseurl'] ) . 'myplugin';
}
```

### Why writing to the plugin folder is forbidden

- Auto-update wipes the entire plugin directory and re-extracts the ZIP. Anything you wrote there is gone.
- Files inside `wp-content/plugins/your-plugin/` are served by the web server. Writing user data there exposes it (cache files with auth tokens, generated MP3s with private content, etc.).
- Many production hosts make the plugins directory read-only; your write silently fails.
- wp.org review will flag this immediately.

### `wp_handle_upload()` vs. `media_handle_upload()`

Use these instead of moving `$_FILES` yourself. They run all the security checks (MIME, extension blocklist, size, nonce optionally) and place the file under `wp_upload_dir()`.

**`wp_handle_upload()`** — moves the file into uploads, returns metadata, but does *not* create a database row.

```php
if ( ! function_exists( 'wp_handle_upload' ) ) {
    require_once ABSPATH . 'wp-admin/includes/file.php';
}

$result = wp_handle_upload(
    $_FILES['my_file'],
    [ 'test_form' => false ] // we're not inside an admin form, so skip the form action check
);

if ( isset( $result['error'] ) ) {
    wp_die( esc_html( $result['error'] ) );
}
// $result = [ 'file' => '/abs/path', 'url' => '...', 'type' => 'image/png' ]
```

**`media_handle_upload()`** — calls `wp_handle_upload()` *and* creates an attachment post (so the file shows up in Media Library, gets sub-sizes generated, extracts EXIF/ID3, etc.).

```php
require_once ABSPATH . 'wp-admin/includes/image.php';
require_once ABSPATH . 'wp-admin/includes/file.php';
require_once ABSPATH . 'wp-admin/includes/media.php';

$attachment_id = media_handle_upload( 'my_file', $post_id );

if ( is_wp_error( $attachment_id ) ) {
    wp_die( esc_html( $attachment_id->get_error_message() ) );
}
// $attachment_id is now a real attachment post ID.
```

Rule of thumb: if the uploaded file should appear in the Media Library, use `media_handle_upload()`. If it's an internal artifact (a cache file, a generated thumbnail or export file that you're storing per-post), use `wp_handle_upload()` or write directly via `wp_upload_dir()` + `wp_mkdir_p()`.

### Permission and writability checks

```php
$upload = wp_upload_dir();

if ( ! empty( $upload['error'] ) ) {
    return new WP_Error( 'upload_dir', $upload['error'] );
}
if ( ! wp_is_writable( $upload['basedir'] ) ) {
    return new WP_Error( 'not_writable', 'Uploads directory is not writable.' );
}
```

Prefer `wp_is_writable()` over the raw PHP `is_writable()` — it handles a Windows-specific edge case where `is_writable()` reports incorrectly on read-only files.

---

## 5. REST API `permission_callback`

The single most common REST-related rejection: omitting `permission_callback`, or setting it to `null`. Since WordPress 5.5 this triggers a `_doing_it_wrong` notice and may be hard-blocked in the future.

### Signature

```php
register_rest_route(
    string $namespace,   // e.g. 'myplugin/v1' — never just 'v1', never empty
    string $route,       // e.g. '/items/(?P<id>\d+)'
    array  $args         // methods, callback, permission_callback, args, ...
);
```

Always register inside the `rest_api_init` action:

```php
add_action( 'rest_api_init', 'myplugin_register_routes' );

function myplugin_register_routes() {
    register_rest_route( 'myplugin/v1', '/items', [
        'methods'             => WP_REST_Server::READABLE,    // GET
        'callback'            => 'myplugin_get_items',
        'permission_callback' => '__return_true',             // intentionally public
    ] );

    register_rest_route( 'myplugin/v1', '/items', [
        'methods'             => WP_REST_Server::CREATABLE,   // POST
        'callback'            => 'myplugin_create_item',
        'permission_callback' => function () {
            return current_user_can( 'edit_posts' );
        },
    ] );
}
```

### Why `permission_callback` must always be set

- It runs *before* your callback, so it's your one chance to reject unauthenticated/unauthorized requests cleanly.
- Omitting it is treated as a programming error by core and surfaces in debug logs.
- A `null` callback is treated the same as missing — it does **not** mean "public." Use `__return_true` for that.
- Review reviewers grep for `register_rest_route` and check every result for a non-null permission callback.

### `__return_true` for intentionally public endpoints

Only use this when the data really is public-by-design (e.g. a published-post lookup that mirrors what the front-end already shows):

```php
'permission_callback' => '__return_true',
```

Add a code comment explaining *why* it's public — this helps reviewers and future you.

### `current_user_can()` for protected endpoints

Check capabilities, not roles. Capabilities are stable across role customizations and multisite super-admin overrides; role names aren't.

```php
// Admin-only endpoint.
'permission_callback' => function () {
    return current_user_can( 'manage_options' );
},

// Per-resource check (note the second arg).
'permission_callback' => function ( WP_REST_Request $request ) {
    $post_id = (int) $request['id'];
    return current_user_can( 'edit_post', $post_id );
},
```

Avoid checks like `wp_get_current_user()->roles[0] === 'administrator'` — they fail for super admins, custom roles, and multisite.

### Nonces are separate from `permission_callback`

The REST API authenticates logged-in cookie requests via the `X-WP-Nonce` header (or `_wpnonce` query param) with action `wp_rest`. The `permission_callback` checks *authorization* (can this user do the thing); the nonce checks *authenticity* (is the request really from a logged-in session). Both run — you don't manually call `wp_verify_nonce()` inside a REST callback for the standard cookie auth case.

For non-cookie auth (Application Passwords, OAuth), the nonce isn't required; the auth header authenticates the user, and your `permission_callback` still runs.

```js
// Browser-side (admin or front-end with wp-api enqueued):
wp.apiFetch( {
    path: '/myplugin/v1/items',
    method: 'POST',
    data: { title: 'hello' }
} );
// apiFetch automatically attaches the X-WP-Nonce header.
```

### Return a `WP_Error` for custom denial messages

```php
'permission_callback' => function () {
    if ( ! is_user_logged_in() ) {
        return new WP_Error(
            'rest_not_logged_in',
            __( 'You must be logged in.', 'myplugin' ),
            [ 'status' => 401 ]
        );
    }
    if ( ! current_user_can( 'edit_posts' ) ) {
        return new WP_Error(
            'rest_forbidden',
            __( 'You cannot edit items.', 'myplugin' ),
            [ 'status' => 403 ]
        );
    }
    return true;
},
```

---

## Quick rejection checklist

Before you submit to wp.org, grep your plugin for these:

- [ ] No `include`/`require` of `wp-load.php`, `wp-config.php`, or `wp-blog-header.php`.
- [ ] No `define( 'ABSPATH', ... )` or other core constant definitions.
- [ ] No hardcoded `wp-content/plugins/my-plugin/...` strings.
- [ ] No `WP_PLUGIN_URL . '/my-plugin'` or `WP_PLUGIN_DIR . '/my-plugin'`.
- [ ] No writes inside `plugin_dir_path( __FILE__ )` — use `wp_upload_dir()`.
- [ ] Every `register_rest_route()` call has a non-null `permission_callback`.
- [ ] Settings live in `wp_options` via `register_setting()`, not in plugin files.
- [ ] Every option has a `sanitize_callback`.
- [ ] All output is escaped (`esc_html`, `esc_attr`, `esc_url`, `wp_kses_post`).
- [ ] All input is sanitized at entry (`sanitize_text_field`, `absint`, etc.).
- [ ] File operations go through `wp_handle_upload()`, `media_handle_upload()`, or `WP_Filesystem`.

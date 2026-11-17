# Plugin Basics, Header & Lifecycle

Compiled from the WordPress Plugin Developer Handbook.

## 1. What a plugin is & how WordPress loads it

Source: https://developer.wordpress.org/plugins/intro/ · https://developer.wordpress.org/plugins/plugin-basics/

**RULE:** A plugin extends WordPress without touching core (core updates overwrite changes).
The minimum viable plugin is **one PHP file in `wp-content/plugins/` with a header comment
containing a Plugin Name**. WordPress scans the `plugins` folder **and one level of sub-folders**
for PHP files with a plugin header.

```php
<?php
/**
 * Plugin Name: My Awesome Plugin
 */
```

Single-file plugins can sit directly in `plugins/`; conventionally a plugin lives in its own
folder with the main file matching the folder name. Distributed plugins must use a
GPLv2-compatible license.

Gotchas: only the top level + one sub-folder level is scanned — don't bury the header file
deeper. Folder/file names must be unique to avoid ecosystem collisions.

## 2. The plugin header

Source: https://developer.wordpress.org/plugins/plugin-basics/header-requirements/

**RULE:** Header is a comment block in the **main PHP file**. The *only* required field is
`Plugin Name`.

```php
<?php
/**
 * Plugin Name:       My Plugin
 * Plugin URI:        https://example.com/my-plugin
 * Description:       Short description (< 140 chars).
 * Version:           1.0.0
 * Requires at least: 5.6
 * Requires PHP:      7.4
 * Author:            Your Name
 * License:           GPLv2 or later
 * License URI:       https://www.gnu.org/licenses/gpl-2.0.html
 * Text Domain:       my-plugin
 * Domain Path:       /languages
 * Requires Plugins:  woocommerce, another-plugin
 * Network:           true
 * Update URI:        https://example.com/my-plugin
 */
```

| Field | Required? | Notes |
|---|---|---|
| `Plugin Name` | **Required** | Only mandatory field |
| `Plugin URI` | Optional | Must be unique; not a wp.org URL |
| `Description` | Optional | < 140 chars |
| `Version` | Optional | `version_compare()`-friendly |
| `Requires at least` / `Requires PHP` | Optional | Min WP / PHP; since WP 5.8 parsed from main file (not readme) |
| `Author` / `Author URI` / `License` / `License URI` | Optional | |
| `Text Domain` / `Domain Path` | Optional | i18n; defaults to slug since WP 4.6 |
| `Network` | Optional | `true` = network-wide multisite |
| `Update URI` | Optional | Controls update source (prevents wp.org slug hijack) |
| `Requires Plugins` | Optional | Comma-separated wp.org **slugs** of dependencies (WP 6.5+) |

Gotchas: `Requires Plugins` takes slugs only, no commas inside a slug. `Plugin URI` must not point
to wordpress.org. `1.02` is NOT greater than `1.1` under `version_compare()`.

## 3. Activation & deactivation hooks

Source: https://developer.wordpress.org/plugins/plugin-basics/activation-deactivation-hooks/

**RULE:** `register_activation_hook( __FILE__, $cb )` / `register_deactivation_hook( __FILE__, $cb )`.
First arg = the **main plugin file**. Activation = setup (tables, default options, rewrite rules).
Deactivation = light cleanup (NOT permanent deletion).

```php
function pluginprefix_activate() {
    pluginprefix_setup_post_type(); // register CPT first
    flush_rewrite_rules();          // then flush
}
register_activation_hook( __FILE__, 'pluginprefix_activate' );
```

Gotchas: `flush_rewrite_rules()` must run AFTER the CPT is registered. Deactivation is not
uninstall — never delete user data here.

## 4. Uninstall: `uninstall.php` vs `register_uninstall_hook`

Source: https://developer.wordpress.org/plugins/plugin-basics/uninstall-methods/

**RULE:** Permanently delete all plugin data on uninstall. Two mutually exclusive options:

1. `uninstall.php` in the plugin root (preferred) — auto-run on delete; MUST guard:
```php
if ( ! defined( 'WP_UNINSTALL_PLUGIN' ) ) { die; }
delete_option( 'wporg_option' );
```
2. `register_uninstall_hook( __FILE__, 'cb' )` — keeps logic in main file (`WP_UNINSTALL_PLUGIN`
   is NOT defined in this path).

Gotchas: if `uninstall.php` exists, the registered hook is ignored — pick one. On multisite,
looping every blog is expensive. Always guard `uninstall.php` against direct access.

## 5. Path & URL functions

Source: https://developer.wordpress.org/plugins/plugin-basics/determining-plugin-and-content-directories/

**RULE:** Never hardcode paths. URLs for assets (enqueue); filesystem paths for `include`/`require`/file I/O.

| Function | Returns |
|---|---|
| `plugin_dir_path( __FILE__ )` | Filesystem path, trailing slash |
| `plugin_dir_url( __FILE__ )` | URL, trailing slash |
| `plugins_url( $path, __FILE__ )` | Full URL to a file |
| `plugin_basename( __FILE__ )` | `folder/file.php` identifier |

Constants `WP_PLUGIN_DIR`, `WP_PLUGIN_URL`, `WP_CONTENT_DIR/URL` have **no** trailing slash. Site
helpers: `site_url()`, `home_url()`, `admin_url()`, `content_url()`, `wp_upload_dir()`; multisite
variants `network_site_url()`, `network_admin_url()`.

Gotchas: mixing path (filesystem) and URL functions is the #1 mistake. `require plugins_url(...)`
fails.

## 6. Including PHP files & best practices

Source: https://developer.wordpress.org/plugins/plugin-basics/best-practices/

**RULE:** Build include paths from `plugin_dir_path( __FILE__ )` / `__DIR__`. Load admin-only code
conditionally. Prefix every global symbol with a unique 4–5+ char prefix; wrap in classes/
namespaces; guard against redeclaration; block direct access.

```php
require_once plugin_dir_path( __FILE__ ) . 'includes/class-core.php';
if ( is_admin() ) { require_once __DIR__ . '/admin/admin.php'; }

if ( ! defined( 'ABSPATH' ) ) { exit; } // block direct access
```

Recommended structure: `plugin-name.php`, `uninstall.php`, `/languages`, `/includes`, `/admin`,
`/public`.

Gotchas: NEVER use reserved prefixes `wp_`, `__`, `_`, `WordPress`. Unprefixed names are the
leading cause of fatal conflicts. Missing `ABSPATH` guard exposes files to direct browser access.

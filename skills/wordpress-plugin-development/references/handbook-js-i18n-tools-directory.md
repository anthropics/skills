# JavaScript/Ajax, i18n, Developer Tools & the wp.org Directory

Compiled from the WordPress Plugin Developer Handbook.

## 1. Enqueuing scripts & styles

Source: https://developer.wordpress.org/plugins/javascript/enqueuing/

**RULE: never hardcode `<script>`/`<link>` tags** — always enqueue. Hook the enqueue:
`wp_enqueue_scripts` (front-end), `admin_enqueue_scripts` (admin; callback gets `$hook` — bail if
not your page), `login_enqueue_scripts`.

```php
wp_enqueue_script( $handle, $src, $deps, $ver, $args );
// $src: plugins_url('/js/x.js', __FILE__) — never a hardcoded URL
// $args (WP 6.3+): array( 'in_footer' => true, 'strategy' => 'defer'|'async' )  (legacy: bool $in_footer)
wp_enqueue_style( $handle, $src, $deps, $ver, $media );
```
```php
add_action( 'admin_enqueue_scripts', function ( $hook ) {
    if ( 'toplevel_page_myplugin' !== $hook ) return;
    wp_enqueue_script( 'myplugin', plugins_url( '/js/app.js', __FILE__ ),
        array( 'jquery' ), '1.0.0', array( 'in_footer' => true ) );
} );
```
`wp_register_script/style()` define without printing; `wp_enqueue_*` prints. Pass data:
`wp_localize_script($handle,$obj,$data)`, `wp_add_inline_script($handle,$js,'before'|'after')`,
`wp_set_script_translations($handle,'text-domain',$path)`.

Gotchas: localize/translations calls must run after the script is registered. Top-level admin hook
is `toplevel_page_{slug}`; submenu `{parent}_page_{slug}`. Bump `$ver` to bust caches.

## 2. jQuery

Source: https://developer.wordpress.org/plugins/javascript/jquery/

**RULE: WordPress jQuery runs in `noConflict` — global `$` is unavailable.** Use `jQuery` or alias:
```javascript
( function( $ ) { $( '.pref' ).on( 'change', fn ); } )( jQuery );
```
Declare `array('jquery')` as a dependency; don't bundle your own jQuery.

## 3. Ajax (admin-ajax.php)

Source: https://developer.wordpress.org/plugins/javascript/ajax/

**RULE: classic Ajax POSTs to `wp-admin/admin-ajax.php`; the URL must come from PHP**, every request
carries an `action` and a nonce.
```php
wp_localize_script( 'my-js', 'my_ajax_obj', array(
    'ajax_url' => admin_url( 'admin-ajax.php' ),
    'nonce'    => wp_create_nonce( 'my_nonce_action' ),
) );
add_action( 'wp_ajax_my_tag_count',        'my_tag_count' ); // logged-in
add_action( 'wp_ajax_nopriv_my_tag_count', 'my_tag_count' ); // logged-out (only if needed)
function my_tag_count() {
    check_ajax_referer( 'my_nonce_action' );
    if ( ! current_user_can( 'edit_posts' ) ) wp_send_json_error( 'forbidden', 403 );
    $title = sanitize_text_field( wp_unslash( $_POST['title'] ) );
    wp_send_json_success( array( 'count' => 5 ) ); // ends with wp_die()
}
```
`wp_ajax_{action}` = logged-in; `wp_ajax_nopriv_{action}` = logged-out (register only if anonymous
access is required). **The REST API (`register_rest_route` with `permission_callback`) is the
modern alternative.**

Gotchas: forgetting `wp_die()` returns trailing `0`. Nonce action string must match.

## 4. Internationalization (i18n)

Source: https://developer.wordpress.org/plugins/internationalization/ (+ how-to, localization)

**RULE: text domain == plugin slug, as a LITERAL string — never a variable/constant.**
```php
__( 'Save', 'my-plugin' );   // ✅
__( 'Save', $domain );           // ❌
```
Functions: `__()`/`_e()`; escaping variants `esc_html__()`, `esc_html_e()`, `esc_attr__()`,
`esc_attr_e()`; context `_x()`/`_ex()`; plurals `_n()`/`_nx()`/`_n_noop()`; `number_format_i18n()`,
`date_i18n()`.

**Never interpolate variables — use `printf` with placeholders (numbered for multiple args):**
```php
printf( /* translators: %s: city */ esc_html__( 'Your city is %s.', 'my-plugin' ), esc_html( $city ) );
printf( /* translators: 1: city 2: zip */ esc_html__( 'City %1$s, zip %2$s.', 'my-plugin' ), $city, $zip );
```
**Since WP 4.6, wp.org-hosted plugins load translations automatically** from
translate.wordpress.org — `load_plugin_textdomain()` is largely unnecessary. JS: 
`wp_set_script_translations()`. Pipeline: `.pot` → `.po` → `.mo`; generate with
`wp i18n make-pot . languages/my-plugin.pot`.

Gotchas: add `/* translators: ... */` immediately before the call. Don't translate empty strings;
avoid markup in translatable strings; translations don't load before `init`.

## 5. Developer tools

Source: https://developer.wordpress.org/plugins/developer-tools/

Debug constants (wp-config.php): `WP_DEBUG`, `WP_DEBUG_LOG`, `WP_DEBUG_DISPLAY`, `SCRIPT_DEBUG`
(unminified core assets), `SAVEQUERIES`. Tools: **Debug Bar** (+ add-ons), **Query Monitor**,
**Plugin Check (PCP)** — run before submitting/updating.

Gotchas: never leave `WP_DEBUG`/`SCRIPT_DEBUG` on in production; `WP_DEBUG_LOG` requires `WP_DEBUG`.

## 6. WordPress.org Plugin Directory

Source: https://developer.wordpress.org/plugins/wordpress-org/ (+ readme, assets, guidelines, faq)

### readme.txt
Lives in `/trunk/readme.txt`, Markdown subset; validate with the official readme validator. Header:
```
=== My Plugin ===
Contributors: wporg_userid
Tags: audio, accessibility            (max 5)
Requires at least: 4.7
Tested up to: 6.5                     (major WP version, numbers only)
Requires PHP: 7.0
Stable Tag: 4.3
License: GPLv2 or later
```
**Stable Tag is the release switch:** wp.org reads it from `/trunk/readme.txt`, then serves
`/tags/{StableTag}/` (whose readme must also carry the right tag). Displayed **version comes from
the main PHP file's `Version:` header**. `Stable Tag: trunk` is prohibited for new plugins.
Sections: Description, Installation, FAQ, Screenshots, Changelog, Upgrade Notice. Since WP 5.8,
`Requires PHP`/`Requires at least` are parsed from the main PHP file.

### Assets (top-level `assets/` SVN dir, NOT trunk/tags)
Icons `icon-128x128.*` / `icon-256x256.*` / `icon.svg`. Banners `banner-772x250.*` /
`banner-1544x500.*`. Screenshots `screenshot-1.*`, `screenshot-2.*` (lowercase; descriptions map to
the readme Screenshots section).

### SVN release flow
Dirs: `/trunk/` (current code), `/tags/` (releases), `/assets/`, `/branches/`. SVN is a **release**
repo — push finished work only. Tag by copying trunk:
```bash
svn cp trunk tags/1.2.3
svn ci -m "tagging 1.2.3"
```

### Detailed guidelines (terse)
GPLv2+-compatible · responsible for bundled code · stable working version on wp.org · human-
readable code, no obfuscation · **no trialware/locked features in the free plugin** · SaaS allowed
if substantive + documented · **no tracking without explicit opt-in** · no executing externally-
fetched code · no dishonest/black-hat behavior · "Powered by" credits opt-in · no dashboard
hijacking (notices dismissible) · no readme spam (≤5 tags) · use WordPress-bundled libraries · SVN
commits limited to releases · increment version each release · plugin complete at submission ·
respect trademarks.

### Developer FAQ highlights
Slug is permanent after approval (display name changes via the PHP header + readme). Committers get
SVN write access via Advanced; Contributors are listed authors. Closing a plugin is permanent;
SVN stays open for forking. Tag releases with version numbers only.

Gotchas: forgetting to update Stable Tag (or the tag-folder readme) breaks auto-updates. PHP-header
vs readme version mismatch shows the wrong version. `assets/` must NOT live inside trunk. Don't set
`Tested up to` past the current WP release.

# Security — capabilities, validation, sanitizing, escaping, nonces

Compiled from the WordPress Plugin Developer Handbook "Security" chapter (now consolidated into
the Common APIs Security Handbook).

> **Core principle:** Never trust input. *Validate* on the way in, *sanitize* before storing,
> *escape* on the way out. Treat `$_GET`, `$_POST`, `$_REQUEST`, `$_COOKIE`, `$_SERVER`, `$_FILES`
> as untrusted.

## 1. Checking user capabilities

Source: https://developer.wordpress.org/plugins/security/checking-user-capabilities/

**RULE: any data-changing action (admin OR public) checks `current_user_can()` first.**
```php
if ( current_user_can( 'edit_others_posts' ) ) { /* ... */ }
```
**RULE: check by capability, never by role.** Roles are mutable bundles of caps.
```php
// WRONG: if ( 'administrator' === $user->roles[0] )
// RIGHT: if ( current_user_can( 'manage_options' ) )
```
Pick the narrowest cap: `edit_posts` (author), `edit_others_posts` (editor), `manage_options`
(admin). Multisite network actions need `manage_network`, `manage_network_options` etc.; prefer a
specific cap over `is_super_admin()`.

## 2. Data validation

Source: https://developer.wordpress.org/apis/security/data-validation/

**RULE: validation tests data against a pattern (valid/invalid) and does NOT alter it** — distinct
from sanitizing (cleans/changes) and escaping (safe for output). Validate as early as possible.
Prefer an **allowlist** over a blocklist. Use strict comparison.

```php
$allowed = array( 'author', 'post_author', 'date', 'post_date' );
$orderby = sanitize_key( $_POST['orderby'] );
if ( in_array( $orderby, $allowed, true ) ) { /* valid */ }
$id = absint( $_GET['id'] ); // non-negative integer
```
Format checks: `preg_match()`, `ctype_*`, `is_email()`, `term_exists()`, `username_exists()`,
`validate_file()`.

## 3. Securing / sanitizing input

Source: https://developer.wordpress.org/apis/security/sanitizing/

**RULE: sanitize untrusted input before use/storage.** `sanitize_text_field()` checks UTF-8,
strips tags, removes line breaks/tabs/extra whitespace.
**RULE: superglobals are slashed — call `wp_unslash()` BEFORE sanitizing.**
```php
$title = sanitize_text_field( wp_unslash( $_POST['title'] ) );
$email = sanitize_email( wp_unslash( $_POST['email'] ) );
```
Function set: `sanitize_email`, `sanitize_file_name`, `sanitize_hex_color`, `sanitize_html_class`,
`sanitize_key`, `sanitize_meta`, `sanitize_mime_type`, `sanitize_option`, `sanitize_sql_orderby`,
`sanitize_term`, `sanitize_text_field`, `sanitize_textarea_field`, `sanitize_title`,
`sanitize_user`, `sanitize_url`, plus `absint()` and `wp_kses()`/`wp_kses_post()`.

## 4. Securing / escaping output

Source: https://developer.wordpress.org/apis/security/escaping/

**RULE: escape as late as possible — ideally at the `echo`.** Match the function to the context.
```php
echo '<a href="' . esc_url( $url ) . '">' . esc_html( $text ) . '</a>';
```
- `esc_html()` — text between tags
- `esc_attr()` — attribute values
- `esc_url()` — href/src; `esc_url_raw()` for storage/redirects
- `esc_js()` — inline JS (+ `wp_json_encode()`)
- `esc_textarea()` — `<textarea>` content
- `wp_kses()` / `wp_kses_post()` — output that must keep some HTML

Translated echoes use the escaping i18n variants: `esc_html__()`, `esc_html_e()`, `esc_attr__()`,
`esc_attr_e()`, `esc_html_x()`. Exception: when late escaping is impractical (e.g. generated
scripts), escape at build time and name the variable `_escaped`/`_safe`.

## 5. Nonces (CSRF protection)

Source: https://developer.wordpress.org/apis/security/nonces/

**RULE: protect every state-changing request with a nonce tied to a specific action (+ object ID).**
```php
wp_nonce_field( 'delete-comment_' . $comment_id );             // form
$url = wp_nonce_url( $bare_url, 'trash-post_' . $post->ID );    // URL
$n   = wp_create_nonce( 'my-action_' . $post->ID );             // raw token
```
Verify per context:
- `check_admin_referer( $action )` — admin form/URL; checks nonce + referrer; 403 on fail.
- `check_ajax_referer( $action )` — AJAX; checks nonce; dies on fail.
- `wp_verify_nonce( $nonce, $action )` — manual; returns false/1/2.

Lifetime ~12–24h (filter `nonce_life`). **Nonces are NOT authn/authz** — always also call
`current_user_can()`.

## Quick reference

### Input → sanitize
| Context | Function |
|---|---|
| Single-line text | `sanitize_text_field()` |
| Multi-line text | `sanitize_textarea_field()` |
| Email | `sanitize_email()` |
| Key / meta key | `sanitize_key()` |
| Integer ≥ 0 | `absint()` |
| URL (storage) | `sanitize_url()` / `esc_url_raw()` |
| Slug | `sanitize_title()` |
| File name | `sanitize_file_name()` |
| CSS class | `sanitize_html_class()` |
| HTML (post) | `wp_kses_post()` |
| HTML (custom) | `wp_kses()` |
| Always first on superglobals | `wp_unslash()` |

### Output → escape
| Context | Function |
|---|---|
| Text in HTML | `esc_html()` |
| Attribute | `esc_attr()` |
| URL | `esc_url()` |
| Inline JS / JSON-in-attr | `esc_js()` + `wp_json_encode()` |
| `<textarea>` | `esc_textarea()` |
| Keep safe HTML | `wp_kses_post()` / `wp_kses()` |
| Translated echo | `esc_html_e()` / `esc_attr_e()` |

## Common vulnerabilities & WP defenses

- **XSS** — escape late with context-correct `esc_*`; constrain rich HTML with `wp_kses*`.
- **CSRF** — nonces verified by `check_admin_referer`/`check_ajax_referer`.
- **SQLi** — `$wpdb->prepare()` with `%s`/`%d`/`%f`; never concatenate; `sanitize_sql_orderby()` +
  allowlist for ORDER BY/column names.
- **SSRF** — validate/allowlist hosts; use `wp_safe_remote_get()`.
- **Auth bypass** — `current_user_can()` on every privileged action, in addition to nonces.

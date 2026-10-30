# Privacy, Users/Roles, HTTP API & WP-Cron

Compiled from the WordPress Plugin Developer Handbook.

## 1. Privacy & GDPR

Source: https://developer.wordpress.org/plugins/privacy/ (+ exporter, eraser, suggesting policy text)

**Why:** GDPR/CCPA require sites to disclose, export, and erase personal data. Any plugin storing
personal data (emails, IPs, names, analytics, telemetry, cookies/localStorage) must hook into
WordPress's privacy tools.

**RULES**
- If you store personal data, register **both** an exporter and an eraser.
- Disclose third-party sharing/SDKs/telemetry and browser storage in suggested policy text.
- Restrict access to personal data by capability; clean up on uninstall.
- Use `wp_privacy_anonymize_data()` to minimize (e.g. anonymize IPs).

Suggest policy text on `admin_init`:
```php
add_action( 'admin_init', function () {
    if ( ! function_exists( 'wp_add_privacy_policy_content' ) ) return;
    $content = '<p class="privacy-policy-tutorial">Tutorial prose (excluded when copied).</p>'
        . '<strong>' . __( 'Suggested text:' ) . '</strong> '
        . __( 'We store page-view analytics including IP-derived city.', 'my-plugin' );
    wp_add_privacy_policy_content( 'My Plugin', wp_kses_post( wpautop( $content, false ) ) );
} );
```

Exporter via `wp_privacy_personal_data_exporters`, callback `( $email, $page = 1 )` returns
`['data' => [...groups], 'done' => bool]`; paginate while `done` is false.
Eraser via `wp_privacy_personal_data_erasers`, returns
`['items_removed'=>bool,'items_retained'=>bool,'messages'=>[],'done'=>bool]`.

Gotchas: having an exporter but no eraser (or vice-versa) is a common gap. Guard
`wp_add_privacy_policy_content` with `function_exists`, only on `admin_init`. Paginate large
datasets via `$page` or they time out.

## 2. Users, roles & capabilities

Source: https://developer.wordpress.org/plugins/users/ (+ roles-and-capabilities, working-with-users, user-metadata)

A *role* is a named bucket of *capabilities*. Default roles: Super Admin, Administrator, Editor,
Author, Contributor, Subscriber. Principle of least privilege.

**RULE — check capabilities, not roles.**
```php
if ( current_user_can( 'edit_posts' ) ) { /* ... */ }
```
Manage roles/caps (run on activation, not every load — `add_role` only writes the first time):
```php
add_role( 'myplugin_manager', 'My Plugin Manager', array( 'read' => true, 'manage_myplugin' => true ) );
get_role( 'editor' )->add_cap( 'manage_myplugin' );
```
Read users: `wp_get_current_user()`, `get_current_user_id()`, `get_userdata( $id )`.
Create/update/delete: `wp_create_user()`, `wp_insert_user()` (returns ID or `WP_Error`),
`wp_update_user()`, `wp_delete_user( $id, $reassign )` (**if `$reassign` is invalid, the user's
content is deleted**). Check `username_exists()`/`email_exists()` first; handle `is_wp_error()`.
User meta: `add/update/get/delete_user_meta()` (same single/array semantics as post meta).

Gotchas: `$user->roles[0] === 'administrator'` is wrong — check the cap. `get_user_meta(..., false)`
returns an array. Re-running `add_role()` won't add new caps on upgrade — use `get_role()->add_cap()`.

## 3. HTTP API

Source: https://developer.wordpress.org/plugins/http-api/

**RULE — use the HTTP API, never raw cURL / `file_get_contents()`** (honors proxy settings,
required for wp.org). **Prefer `wp_safe_remote_*`** for any user-influenced URL (SSRF protection).

Functions: `wp_remote_get/post/head/request()` and safe twins `wp_safe_remote_*`. Read with
`wp_remote_retrieve_body()`, `wp_remote_retrieve_response_code()`, `wp_remote_retrieve_header()`.
Always `is_wp_error()` first.

```php
$res = wp_safe_remote_post( 'https://api.example.com/v1/items', array(
    'timeout' => 15,
    'headers' => array( 'Content-Type' => 'application/json', 'Authorization' => 'Bearer ' . $token ),
    'body'    => wp_json_encode( array( 'name' => $name ) ),
) );
if ( is_wp_error( $res ) ) return $res;
$code = wp_remote_retrieve_response_code( $res );
$body = wp_remote_retrieve_body( $res );
```

Gotchas: default `timeout` is 5s. `is_wp_error()` only catches transport failures — a 4xx/5xx still
returns a normal array, so check the response code. Never `sslverify => false`. **Phoning home:**
wp.org forbids sending site data externally without explicit informed opt-in; default-on telemetry
is a violation. `body` as array sends form-encoded; for JSON use `wp_json_encode()` + set
`Content-Type`.

## 4. WP-Cron

Source: https://developer.wordpress.org/plugins/cron/ (+ understanding, scheduling, system-task-scheduler)

**Key fact:** WP-Cron is **request-triggered, not a real daemon** — events fire on page loads.
Guarantees eventual, never precise, timing. Default intervals: `hourly`, `twicedaily`, `daily`,
`weekly` (WP 5.4+). Intervals are in **seconds**.

Custom interval:
```php
add_filter( 'cron_schedules', function ( $s ) {
    $s['fifteen_minutes'] = array( 'interval' => 15 * MINUTE_IN_SECONDS,
        'display' => esc_html__( 'Every 15 Minutes', 'my-plugin' ) );
    return $s;
} );
```

**RULE: register the `cron_schedules` filter AND `add_action(event → callback)` at load time** (the
callback must exist whenever cron fires), and guard scheduling with `wp_next_scheduled()`:
```php
add_action( 'my_cron_hook', 'my_cron_task' );          // every request
if ( ! wp_next_scheduled( 'my_cron_hook' ) ) {
    wp_schedule_event( time(), 'fifteen_minutes', 'my_cron_hook' );
}
```
Also: `wp_schedule_single_event()`, `wp_unschedule_event()`, `wp_clear_scheduled_hook()`.
Unschedule on deactivation. Replace with real cron on busy sites:
`define('DISABLE_WP_CRON', true);` + OS scheduler hitting `wp-cron.php?doing_wp_cron`.

Gotchas: scheduling only in the activation hook without registering the callback at load → cron
fires with no handler. Re-scheduling without `wp_next_scheduled()` stacks duplicates. Registering
`cron_schedules` only on activation breaks rescheduling. WP-Cron is unsuitable for time-critical
jobs.

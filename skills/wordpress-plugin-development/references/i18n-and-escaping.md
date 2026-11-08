# WordPress.org Plugin Review: i18n and Output Escaping

Rules-of-the-road extracted from the official WordPress developer docs. wp.org reviewers reject plugins that violate these — treat each rule as load-bearing.

## Part 1 — Internationalization

### 1.1 Why the rules are strict

Gettext is a static-extraction system. Tools like `makepot`/WP-CLI's `i18n make-pot` scan source files with a parser, not a runtime. If a translatable string or its text domain is anything other than a string literal at the call site, the extractor cannot see it and the translation is lost. wp.org reviewers run the same tooling.

### 1.2 The text domain rule

The text domain **MUST be a single-quoted string literal** that exactly matches the plugin slug (folder name on wp.org). Lowercase, dashes only — no underscores, no spaces, no variables, no constants, no concatenation.

```php
// WRONG — variable as domain
__( 'Save changes', $this->domain );

// WRONG — constant as domain
__( 'Save changes', TEXT_TO_AUDIO_TEXT_DOMAIN );

// WRONG — underscores / wrong slug
__( 'Save changes', 'text_to_audio' );

// RIGHT
__( 'Save changes', 'my-plugin' );
```

The plugin header should declare it (optional since 4.6 but recommended):

```
/* Text Domain: my-plugin */
/* Domain Path: /languages */
```

### 1.3 The message-string rule

The first argument **MUST be a string literal**. No variables, no concatenation, no ternaries, no `sprintf` inside the gettext call.

```php
// WRONG — interpolated variable
__( "Hello $name", 'my-plugin' );

// WRONG — concatenation
__( 'Hello ' . $name, 'my-plugin' );

// WRONG — variable as message
__( $message, 'my-plugin' );

// RIGHT — placeholder, formatted outside
printf(
    /* translators: %s: user display name */
    esc_html__( 'Hello %s', 'my-plugin' ),
    esc_html( $name )
);
```

### 1.4 Full gettext function list

Retrieval (return value):
- `__( $text, $domain )` — translate, return
- `_x( $text, $context, $domain )` — translate with disambiguation context
- `_n( $single, $plural, $number, $domain )` — pluralized
- `_nx( $single, $plural, $number, $context, $domain )` — plural + context
- `_n_noop( $single, $plural, $domain )` — deferred plural for storage in arrays
- `_nx_noop( $single, $plural, $context, $domain )` — deferred plural + context
- `translate_nooped_plural( $nooped, $count, $domain )` — resolve a noop

Echo variants: `_e()`, `_ex()`.

Escape-and-translate (always prefer these in output contexts):
- `esc_html__()`, `esc_html_e()`, `esc_html_x()`
- `esc_attr__()`, `esc_attr_e()`, `esc_attr_x()`

Locale-aware formatters: `number_format_i18n()`, `date_i18n()`.

### 1.5 The `/* translators: */` comment

Whenever a string contains `%s`, `%d`, `%1$s`, etc., place a translator comment immediately above the gettext call. wp.org and core both flag missing comments.

```php
/* translators: %s: number of files generated */
$msg = sprintf( esc_html__( '%s files generated.', 'my-plugin' ), $count );

/* translators: 1: post title, 2: author name */
$msg = sprintf(
    esc_html__( '%1$s by %2$s', 'my-plugin' ),
    esc_html( $title ),
    esc_html( $author )
);
```

Use numbered placeholders (`%1$s`, `%2$s`) whenever there are two or more — translators must be able to reorder them.

### 1.6 `load_plugin_textdomain()` and the 6.7+ notice

Loader signature:

```php
add_action( 'init', 'myplugin_load_textdomain' );
function myplugin_load_textdomain() {
    load_plugin_textdomain(
        'my-plugin',
        false,
        dirname( plugin_basename( __FILE__ ) ) . '/languages'
    );
}
```

Rules:
- Hook on `init`, **never** earlier (`plugins_loaded` is now too early).
- Do not call any gettext function before `init` fires. WordPress 6.7 introduced a `_doing_it_wrong` notice titled **"Translation loading triggered too early"** / `_load_textdomain_just_in_time` whenever a `__()`-family call runs before `init`. Common culprits: translatable strings in class constructors, in plugin-header bootstrap, in `register_activation_hook` callbacks, or inside files loaded by autoload.
- For wp.org-hosted plugins with translations on translate.wordpress.org, the loader is technically optional from 4.6+, but keeping it is harmless and supports sideloaded `.mo`/`.l10n.php` files.

### 1.7 Common mistakes reviewers reject

| Mistake | Fix |
| --- | --- |
| Variable as text — `__( $msg, ... )` | Hard-code the literal, parameterize with `%s` |
| Variable as domain — `__( 'x', $domain )` | Hard-code `'my-plugin'` |
| Mismatched domain across files | Grep the whole plugin; one literal everywhere |
| Missing escape wrapper in output — `_e( ... )` inside HTML | Use `esc_html_e()` / `esc_attr_e()` |
| Concatenating two `__()` calls | Use one string with placeholders |
| Empty string `__( '', ... )` | Never translate the empty string (returns metadata) |
| `\r\n` line endings in messages | Use `\n` only |
| Calling gettext before `init` | Defer; or wrap in an `init`-hooked callback |

---

## Part 2 — Output Escaping

### 2.1 Late-escape rule

Escape at the point of output. Not at assignment, not at function entry, not in a helper four calls up. Reviewers and static scanners verify the **last expression before `echo`/`return`**.

```php
// WRONG — escaped early, mutated later
$url = esc_url( $raw_url );
$url .= '?token=' . $token;          // now unsafe again
echo '<a href="' . $url . '">';

// RIGHT
echo '<a href="' . esc_url( $raw_url . '?token=' . $token ) . '">';
```

### 2.2 The four primary families

| Function | Use for | Example |
| --- | --- | --- |
| `esc_html()` | Text between tags | `<p><?php echo esc_html( $title ); ?></p>` |
| `esc_attr()` | Quoted attribute values | `<div class="<?php echo esc_attr( $cls ); ?>">` |
| `esc_url()` | `href`, `src`, `action`, any URL | `<a href="<?php echo esc_url( $u ); ?>">` |
| `esc_js()` | Inline JS string literals / `data-json` | `<button onclick="doX('<?php echo esc_js( $v ); ?>')">` |

Also: `esc_textarea()` for textareas, `esc_xml()` / `ent2ncr()` for XML feeds.

```php
// WRONG — esc_attr on a URL strips/encodes incorrectly and misses URL-specific filtering
<a href="<?php echo esc_attr( $url ); ?>">

// RIGHT
<a href="<?php echo esc_url( $url ); ?>">
```

### 2.3 Translate + escape combos

Inside HTML output always prefer the escape-aware variant. `_e()` and `__()` alone in markup is a review flag.

```php
// WRONG
<button><?php _e( 'Submit', 'my-plugin' ); ?></button>
<input value="<?php _e( 'Save', 'my-plugin' ); ?>">

// RIGHT
<button><?php esc_html_e( 'Submit', 'my-plugin' ); ?></button>
<input value="<?php esc_attr_e( 'Save', 'my-plugin' ); ?>">

// With context disambiguation
<th><?php echo esc_html_x( 'Post', 'column header', 'my-plugin' ); ?></th>
```

### 2.4 When `wp_kses_post()` / `wp_kses()` is correct

Use these only when you need to **emit HTML you do not control** but want to preserve a known-safe subset. Stripping with `esc_html()` would mangle markup, so you allow-list instead.

Good fits:
- Freemius notice/dialog HTML returned by the SDK
- Admin notice bodies that legitimately include `<a>`, `<strong>`, `<code>`
- Button HTML assembled from settings that may include an `<svg>` icon

```php
// Freemius / notice content — allow post-grade HTML
echo wp_kses_post( $freemius_message );

// Tight allow-list for a specific surface
echo wp_kses(
    $snippet,
    array(
        'a'      => array( 'href' => array(), 'title' => array(), 'rel' => array() ),
        'strong' => array(),
        'em'     => array(),
        'br'     => array(),
    )
);
```

Never use `wp_kses_post()` as a lazy "escape everything" — it permits `<a>`, `<img>`, inline styles, etc.

### 2.5 Shortcode callbacks

Shortcodes **return** their output (do not echo). The returned string is inserted into post content verbatim by `do_shortcode()` — your callback is responsible for escaping every dynamic piece.

```php
// WRONG — raw attribute interpolated into HTML
function myplugin_button( $atts ) {
    return '<button class="' . $atts['class'] . '">Click me</button>';
}

// RIGHT
function myplugin_button( $atts ) {
    $atts = shortcode_atts( array( 'class' => '' ), $atts, 'myplugin_button' );
    return sprintf(
        '<button class="%s">%s</button>',
        esc_attr( $atts['class'] ),
        esc_html__( 'Click me', 'my-plugin' )
    );
}
```

### 2.6 `the_content` filter callbacks

Anything appended to `the_content` is echoed inside post HTML. Escape the dynamic parts; allow-list any HTML you assemble.

```php
add_filter( 'the_content', 'myplugin_prepend_button' );
function myplugin_prepend_button( $content ) {
    $button = sprintf(
        '<button data-id="%d">%s</button>',
        (int) get_the_ID(),
        esc_html__( 'Read more', 'my-plugin' )
    );
    return $button . $content;   // $content is already filtered/escaped by core
}
```

### 2.7 Block `render_callback`

Server-rendered blocks return a string of HTML. Same rule as shortcodes — escape every attribute, allow-list any rich HTML.

```php
function myplugin_render_block( $attributes ) {
    $label = isset( $attributes['label'] ) ? $attributes['label'] : '';
    $color = isset( $attributes['color'] ) ? $attributes['color'] : '#000';

    return sprintf(
        '<div class="myplugin-block" style="color:%1$s">%2$s</div>',
        esc_attr( $color ),
        esc_html( $label )
    );
}
```

### 2.8 XSS vectors a reviewer will probe

- `$_GET` / `$_POST` / `$_REQUEST` / `$_SERVER['REQUEST_URI']` echoed without escaping
- Settings values printed in admin forms without `esc_attr()`
- User-supplied URLs (`href`, `src`, redirect targets) not run through `esc_url()`
- AJAX/REST responses that echo HTML built from request input
- Translation calls inside HTML without the `esc_*_e` wrapper (translators can become an injection vector)
- JSON blobs in `data-*` attributes without `esc_attr()` (and `wp_json_encode()` — never raw `json_encode`)
- Inline `<script>var x = <?php echo $v; ?>` — use `wp_json_encode()` plus `esc_js()` if interpolated
- Admin notices built from option values — wrap with `wp_kses_post()` or escape per-field

### 2.9 Quick decision tree

```
Output is text inside tags?            esc_html / esc_html_e
Output is an attribute value?          esc_attr / esc_attr_e
Output is a URL?                       esc_url
Output is inline JS or JSON-in-attr?   esc_js (and wp_json_encode for objects)
Output is trusted-shape HTML?          wp_kses_post  (or wp_kses with allow-list)
Output is from the_content?            already escaped — do not double-escape
```

---

## Part 3 — Combined checklist before submitting to wp.org

- [ ] Every `__`/`_e`/`_n`/`_x` call uses a single string literal as message and `'<slug>'` as domain
- [ ] No gettext call fires before `init` (no 6.7 just-in-time notice in `debug.log`)
- [ ] Every `%s`/`%d` string has a `/* translators: */` comment
- [ ] Every HTML output context uses an `esc_*` function on dynamic data
- [ ] No `_e()` or bare `__()` left inside template HTML
- [ ] `esc_url()` (not `esc_attr()`) on every URL attribute
- [ ] `wp_kses_post()` only where rich HTML is intentional (Freemius, button HTML)
- [ ] Shortcode and block render callbacks return fully escaped strings
- [ ] No `$_GET`/`$_POST` echoed without escape + nonce + capability check

# Plugin Check + Library Prefixing — Reference

A field guide for shipping a plugin that survives the wp.org review queue. Covers the Plugin Check tool, how the review team operates, and how to prefix vendored PHP libraries so your plugin does not break sites that ship other plugins using the same dependency.

---

## Plugin Check (PCP)

### What it is

Plugin Check is the WordPress.org-published tool that runs the same automated checks the review team runs against submissions. It does not replace the human reviewer, but every modern rejection email leans on its output, and the team confirmed in October 2025 that PCP now runs automatic security scans on every plugin **update** as well as new submissions. If your build fails PCP locally, expect the review team's internal scanner to fail it the same way.

The plugin is published by WordPress.org, requires WordPress 6.3+ and PHP 7.4+, and is developed in the open at https://github.com/WordPress/plugin-check/.

### Installing

```bash
# WP admin
# Plugins > Add New > search "Plugin Check" > Install > Activate

# wp-cli on a working site
wp plugin install plugin-check --activate

# From GitHub (latest trunk, useful if you want the bleeding-edge checks)
git clone https://github.com/WordPress/plugin-check.git wp-content/plugins/plugin-check
wp plugin activate plugin-check
```

### Running before submission

From the admin UI: `Tools > Plugin Check`. You need `manage_plugins` capability. The screen lets you pick which check categories to run, run them, and export results as CSV / JSON / Markdown or Excel.

From the CLI:

```bash
# Check an installed plugin by main file or slug
wp plugin check hello.php
wp plugin check my-plugin

# Check a plugin from disk that is not installed
wp plugin check /path/to/my-plugin

# Check from a URL
wp plugin check https://example.com/my-plugin.zip

# Only static checks run by default under wp-cli.
# To also run runtime checks, preload the plugin's cli.php:
wp plugin check hello.php \
  --require=./wp-content/plugins/plugin-check/cli.php

# Filter by category, ignore specific sniff codes, get a stricter exit:
wp plugin check my-plugin --categories=plugin_repo,security
wp plugin check my-plugin --ignore-codes=WordPress.WP.I18n.MissingTranslatorsComment
wp plugin check my-plugin --format=json --severity=7
```

### What it catches

Checks are grouped into categories. The `plugin_repo` category is the one that maps to wp.org submission requirements; the rest are best-practice. Categories include:

- **Plugin repo / general** — readme.txt presence, Stable Tag, plugin headers (Name, Plugin URI, Description, Author URI, Requires at least, Requires PHP, Requires Plugins), license validation (GPLv2+, Apache, MIT, ISC, MPL-2.0, WTFPL, Unlicense), trademark conflicts in slug/name, forbidden plugin headers, restricted contributors, "Tested up to" mismatch between header and readme.
- **Security** — `WordPress.Security.ValidatedSanitizedInput` (missing sanitization), nonce verification including insecure `wp_verify_nonce()` usage, direct database queries that bypass `$wpdb` helpers, direct file access guards (`ABSPATH` constant), forbidden functions (`exec`, `passthru`, `proc_open`, `shell_exec`, `move_uploaded_file`, `eval`-flavored constructs), `ALLOW_UNFILTERED_UPLOADS` use, `parse_str()` without a second argument, `wp_safe_redirect` over `wp_redirect`.
- **Internationalization** — text-domain mismatches, missing translator comments, `load_plugin_textdomain()` call (now warning — wp.org loads translations automatically).
- **Performance** — non-blocking script enqueues (missing `defer`/`async`), enqueued styles size, enqueued resources from CDN.
- **Accessibility** — image alt and labeling sniffs.
- **Code quality / "prefixing"** — function and class name prefixing, restricted classes / functions, code obfuscation, heredoc/nowdoc usage, minified file detection, AI instructions / dev-only directories left in the ZIP, External Admin Menu Links, Plugin Update Checker (PUC) detection, mismatched "Tested up to" between plugin header and readme.

### Reading pass / warn / error

Output has three tiers:

- **Error** — blocks approval if it is in the `plugin_repo` category. Fix before submitting.
- **Warning** — best-practice issue. Some warnings are now upgraded to errors during human review (especially missing sanitization, missing escaping, trademark conflicts).
- **Low severity error / warning** — surfaced with the CLI flag below.

```bash
# Show low-severity entries too
wp plugin check my-plugin --include-low-severity
```

### Common warnings developers ignore that turn into rejections

- **`WordPress.Security.ValidatedSanitizedInput`** on `$_GET` / `$_POST`. Flagged as a warning by PHPCS, treated as a hard block by reviewers.
- **`WordPress.Security.EscapeOutput`** — every echoed value must pass through `esc_html`, `esc_attr`, `esc_url`, `wp_kses_post`, etc.
- **Trademark in slug** — `woo-…`, `wp-…`, `wordpress-…`, `elementor-…`, `gutenberg-…`, brand names. Previously borderline names now fail.
- **`load_plugin_textdomain()` still being called** — converted to a warning; reviewers still ask you to remove it.
- **Forbidden / discouraged PHP functions** — `eval`, `create_function`, `assert`, `extract`, base64-encoded payloads (read as obfuscation).
- **Minified JS / CSS without sources** — you must ship the readable source or it reads as obfuscation.
- **External admin menu links** — top-level admin menu items that point off-site fail the check.
- **PUC (Plugin Update Checker) calls** — wp.org does not allow self-updating plugins from the directory.
- **"Tested up to" too low or too high** — must be the current major release, not a future one and not three versions behind.

---

## Plugins Team communications

### Review process in brief

1. You upload a ZIP at https://wordpress.org/plugins/developers/add/.
2. The Internal Scanner (which embeds PCP) runs immediately. As of August 2025 the team reported that ~85% of first reviews are now automated.
3. A human reviewer reads the scanner output and your code.
4. You receive a reply from `plugins@wordpress.org`. Replies come from that address.
5. You reply to the same email thread with a fixed ZIP attached, or push a new SVN tag and reply confirming the version number. Do not open a second submission; reply on the existing thread.

### Where re-review requests go

- Reply directly to the `plugins@wordpress.org` thread.
- For policy clarifications (not your specific submission) use the comments on the relevant post at https://make.wordpress.org/plugins/ or the `#pluginreview` channel on the Making WordPress Slack.
- The 500+ submissions/week throughput means turnaround is days to weeks, not hours. Do not nudge before five business days.

### What has shifted recently

- **July 2025** — readme.txt must be written in English as the base language. Localized readmes go through translate.wordpress.org, not the ZIP.
- **August 2025** — Plugin Rollout (phased releases) launched, allowing 24-hour staggered auto-updates.
- **October 2025** — PCP now runs automatic security reports on every plugin **update**, not just new submissions. Updates can now be flagged the same way submissions are.
- **2025 retrospective** — 12,713 plugins reviewed (+40.6% YoY), 69.5% approval rate, 10+ new code-quality checks added (including prefixing) and 5+ new security checks (nonces, direct DB queries, forbidden functions, minified-file detection, `wp_safe_redirect`).

---

## Why prefix vendored PHP libraries

### The shared-execution-space problem

Every active plugin loads into the same PHP process. If plugin A bundles Guzzle 5 under the `GuzzleHttp\` namespace and plugin B bundles Guzzle 7 under the **same** namespace, whichever loads first wins. The loser either gets the wrong class definitions and crashes with `Fatal error: Cannot declare class GuzzleHttp\Client, because the name is already in use`, or worse, silently calls methods with mismatched signatures.

This is the single most common cause of "site went white after activating your plugin" support tickets, and the wp.org code-quality "prefixing" check exists specifically to flag it.

### When prefixing is required vs not

- **Required**: any third-party library you ship under `vendor/` — Freemius SDK, Guzzle, Monolog, Symfony components, league/* packages, action-scheduler when bundled, anything you `composer require`d that is not WordPress core.
- **Not required**: your own code that already lives under a unique vendor namespace (e.g. `MyCompany\MyPlugin\…`). PSR-4 namespaces you control are fine.
- **Not required**: dependencies that WordPress core already ships (don't bundle them at all — there's an explicit check for re-bundling core libraries).

### The class_exists / function_exists fallback pattern

For a single small helper you don't want to prefix, you can guard it:

```php
if ( ! class_exists( '\\Acme\\Helper' ) ) {
    require_once __DIR__ . '/lib/helper.php';
}

if ( ! function_exists( 'acme_format_money' ) ) {
    require_once __DIR__ . '/lib/format-money.php';
}
```

This is a poor substitute for prefixing because:

- The version that wins is whichever plugin loads first — usually arbitrary.
- If two plugins ship different API surfaces under the same class name, one of them will crash at call sites.
- It does not work for namespaced classes with autoloaders — by the time `class_exists` fires, the autoloader may already have committed.

Use it only for tiny, version-stable helpers. For real dependencies, prefix.

---

## Strauss (recommended for new projects)

Strauss is the maintained successor to Mozart. It prefixes namespaces, classnames, and constants in your `vendor/` tree into a separate output directory so each plugin ships its own isolated copy.

### Install

```bash
composer require --dev brianhenryie/strauss
```

### composer.json config

```json
{
  "require": {
    "freemius/wordpress-sdk": "^2.7"
  },
  "require-dev": {
    "brianhenryie/strauss": "^0.20"
  },
  "extra": {
    "strauss": {
      "target_directory": "vendor-prefixed",
      "namespace_prefix": "Acme\\MyPlugin\\Dependencies\\",
      "classmap_prefix": "Acme_MyPlugin_",
      "constant_prefix": "ACME_MYPLUGIN_",
      "packages": [],
      "update_call_sites": false,
      "include_root_autoload": false,
      "optimize_autoloader": true,
      "exclude_from_copy": {
        "packages": [],
        "namespaces": [],
        "file_patterns": []
      },
      "exclude_from_prefix": {
        "packages": [],
        "namespaces": [],
        "file_patterns": []
      },
      "delete_vendor_packages": true,
      "delete_vendor_files": false
    }
  },
  "scripts": {
    "prefix-namespaces": [
      "strauss",
      "@php composer dump-autoload"
    ],
    "post-install-cmd": ["@prefix-namespaces"],
    "post-update-cmd": ["@prefix-namespaces"]
  }
}
```

Key keys:

- `namespace_prefix` — the namespace every PSR-4 class in vendor gets nested under.
- `target_directory` — where prefixed copies are written. Ship this directory; `.distignore` the original `vendor/`.
- `classmap_prefix` — prefix for non-namespaced (legacy) classes.
- `constant_prefix` — prefix for `define()`d global constants.
- `delete_vendor_files` / `delete_vendor_packages` — clean the original `vendor/` after copying so you can't accidentally autoload both.

### Running

```bash
# After composer install, this runs automatically via the post-install-cmd hook.
# Manual invocation:
vendor/bin/strauss
composer prefix-namespaces

# Dry run to see what would change:
vendor/bin/strauss --dry-run
```

### What it handles

Classes, traits, interfaces, function-style files (Composer `files` autoloaders), and global constants. License files are preserved.

---

## Mozart (legacy)

Mozart was the original tool. It still works, but most new WordPress plugins are migrating to Strauss for the unified output dir and `files` autoloader support.

```json
{
  "require-dev": {
    "coenjacobs/mozart": "^1.2"
  },
  "extra": {
    "mozart": {
      "dep_namespace": "Acme\\MyPlugin\\Dependencies\\",
      "dep_directory": "/vendor-prefixed/",
      "classmap_directory": "/vendor-prefixed/classes/",
      "classmap_prefix": "Acme_MyPlugin_",
      "packages": [
        "freemius/wordpress-sdk"
      ],
      "excluded_packages": [],
      "delete_vendor_directories": true
    }
  }
}
```

Run with `vendor/bin/mozart compose`. Strauss configuration concepts map almost 1:1 — you can migrate by renaming `dep_namespace` → `namespace_prefix`, `dep_directory` → `target_directory`, etc.

---

## PHP-Scoper

PHP-Scoper takes a different angle: rather than copy-and-prefix selected packages, it scopes an **entire build artifact** (typically a PHAR, but also a plain `build/` directory) so every namespace inside the artifact gets a generated prefix.

```bash
composer require --dev humbug/php-scoper

# Or via PHAR
wget https://github.com/humbug/php-scoper/releases/latest/download/php-scoper.phar
```

`scoper.inc.php`:

```php
<?php
use Isolated\Symfony\Component\Finder\Finder;

return [
    'prefix' => 'AcmeMyPluginScoped',
    'finders' => [
        Finder::create()
            ->files()
            ->in('vendor')
            ->name('*.php'),
    ],
    'exclude-namespaces' => [
        'WP_',
        'WordPress\\',
    ],
    'exclude-classes' => ['/^WP_/'],
    'exclude-functions' => ['/^wp_/'],
    'exclude-constants' => ['/^WP_/', '/^ABSPATH$/'],
];
```

Run:

```bash
php-scoper add-prefix --output-dir=build/scoped
php-scoper inspect path/to/some-file.php
```

Best for plugins that ship many libraries or a real PHAR. More setup overhead than Strauss: you write the finder, manage the build output, and re-run autoloader generation against the scoped directory. The PHP-Scoper docs explicitly recommend end-to-end testing of the scoped artifact before release because scoping touches more surface area than Strauss does.

---

## When to use which

- **Strauss** — default recommendation for WordPress plugins with a small `vendor/` (1–10 packages). Composer-native, prefixes only what you tell it to, leaves your own source untouched.
- **PHP-Scoper** — large plugins shipping dozens of libraries, plugins that build a PHAR, plugins where you want everything in vendor scoped including transitive deps you didn't list explicitly.
- **Manual prefixing + `class_exists` guards** — tiny plugins with one or two hand-vendored helper files where the overhead of a composer pipeline isn't worth it.
- **Mozart** — only if you have an existing Mozart pipeline that works. New projects: skip it.

---

## Concrete Freemius example

Freemius SDK is the single most common source of "PHP library conflicts" warnings on wp.org reviews. Every paid plugin using Freemius ships its own copy of the same SDK; without prefixing, the first plugin to load wins and the rest silently hit the wrong SDK code, breaking license activation in ways that look like Freemius bugs but are not.

### Prefixing Freemius with Strauss

```json
{
  "require": {
    "freemius/wordpress-sdk": "^2.7"
  },
  "require-dev": {
    "brianhenryie/strauss": "^0.20"
  },
  "extra": {
    "strauss": {
      "target_directory": "freemius",
      "namespace_prefix": "Acme\\MyPlugin\\Freemius\\",
      "classmap_prefix": "Acme_MyPlugin_FS_",
      "constant_prefix": "ACME_MYPLUGIN_FS_",
      "packages": [
        "freemius/wordpress-sdk"
      ],
      "delete_vendor_packages": true
    }
  }
}
```

Then in your plugin bootstrap, load the prefixed copy:

```php
// Before:
// require_once __DIR__ . '/vendor/freemius/wordpress-sdk/start.php';

// After Strauss has run:
require_once __DIR__ . '/freemius/freemius/wordpress-sdk/start.php';
```

### Caveats — test the license flow end-to-end

- Freemius internally references its own classes by string in several places (option keys, transient names, hook names). Prefixing **class names** is safe; prefixing **option keys or hook names** is not — Strauss does not touch string literals by default, which is the behavior you want.
- The Freemius dashboard / opt-in modal uses globally registered admin pages. After prefixing, verify: install flow, activation, deactivation feedback modal, license key entry, license sync, plan upgrade webhook, and uninstall.
- If you previously shipped an **unprefixed** SDK and users already activated licenses, the option keys may not match after you switch to a prefixed build. Plan a one-time migration that copies the old `fs_*` options to the new prefixed names on upgrade.
- Freemius themselves publish a `freemius/wordpress-sdk-prefix` helper script for plugins that aren't on Composer. If you are on Composer, Strauss is the cleaner integration.

Test on a staging site with a real (sandboxed) Freemius product before pushing the prefixed build to wp.org — a broken license flow is a worse outcome than a "library conflict" warning.

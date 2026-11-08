---
name: wordpress-plugin-development
description: Build WordPress plugins correctly and pass wp.org Plugin Directory review. Covers the full Plugin Developer Handbook (security, hooks, REST, shortcodes, blocks, CPTs/taxonomies, settings/meta, privacy/GDPR, users/roles, HTTP API, WP-Cron, JS/Ajax, i18n, readme/assets/SVN) and the 19 wp.org guidelines that cause closures (trialware, telemetry without opt-in, remote-loaded assets, missing source for minified files, wrong text-domain literal, missing REST permission_callback, vendored library collisions). Use when building a WordPress plugin or fixing a Plugins Team closure, preparing a submission, auditing compliance, responding to Plugin Check warnings, adding REST routes/shortcodes/blocks, registering CPTs/taxonomies/settings/meta, enqueuing scripts, wiring cron or activation hooks, translations, sanitizing/escaping, capability/nonce checks, or bundling PHP libs. Apply proactively on code under `wp-content/plugins/` or when you see `register_rest_route`, `add_shortcode`, `register_post_type`, `register_setting`, `current_user_can`, `esc_html__`, `WP_PLUGIN_DIR`, or Freemius. Skip non-plugin PHP, themes, or pure JS UI.
---

# WordPress Plugin Development & wp.org Guidelines

A field guide for building WordPress plugins correctly and shipping plugins that pass — and stay
on — the wp.org directory. It combines two bodies of knowledge:

1. **wp.org Directory survival** — the Plugins Team review cycle is slow and surprising; catch
   problems before submission, not after closure.
2. **The official Plugin Developer Handbook** — the canonical "how to build it right" reference
   (basics, security, hooks, data APIs, privacy, cron, i18n, etc.), distilled RULE-first.

## When to use this skill

Any time you are reading or writing code under `wp-content/plugins/`. The triggers in the
description are not exhaustive — anything touching WordPress plugin APIs from inside a plugin
folder is fair game.

Skip it for: WordPress theme code (different review track), standalone PHP outside a plugin, pure
JS/front-end work that doesn't touch a plugin's PHP.

## How to use this skill

The body below is a fast-loading triage layer. For the actual rules and code patterns, jump to the
appropriate reference file.

**wp.org directory & compliance (closure-survival):**

| You are working on… | Open this reference |
|---|---|
| The closure email itself, or the master list of guidelines | `references/guidelines.md` |
| Anything translatable, or any echoed/returned HTML | `references/i18n-and-escaping.md` |
| Hooks, paths, settings, uploads, REST routes (compliance angle) | `references/hooks-paths-uploads-rest.md` |
| Running Plugin Check, or prefixing Freemius / vendored libs | `references/plugin-check-and-prefixing.md` |

**Plugin Developer Handbook (how to build it right):**

| You are working on… | Open this reference |
|---|---|
| Plugin header, activation/deactivation/uninstall, paths, structure | `references/handbook-plugin-basics.md` |
| Capabilities, validation, sanitizing, escaping, nonces | `references/handbook-security.md` |
| Actions/filters, admin menus, shortcodes | `references/handbook-hooks-menus-shortcodes.md` |
| Options API, Settings API, post meta, CPTs, taxonomies | `references/handbook-settings-data.md` |
| Privacy/GDPR, users & roles, HTTP API, WP-Cron | `references/handbook-privacy-users-http-cron.md` |
| Enqueuing JS/CSS, jQuery, Ajax, i18n, dev tools, readme/assets/SVN | `references/handbook-js-i18n-tools-directory.md` |

Each reference is self-contained markdown — read the one you need, ignore the rest. The handbook
references are sourced from developer.wordpress.org/plugins/ (verify file:line/API details against
current core, as APIs evolve).

## The 80/20 — what causes most rejections

If you only remember a handful of rules, remember these. They show up in roughly every other closure notice the Plugins Team sends.

1. **No trialware (Guideline 5).** Every feature shipped in the wp.org ZIP must work, fully, with no license check. "Pro features" belong in a separate plugin hosted off wp.org. Locked code in the free ZIP — even unreachable code — is a hard block.
2. **No phoning home without opt-in (Guideline 7).** Any HTTP request that sends user/site/usage data needs an explicit, off-by-default checkbox. Pulling Chart.js from jsDelivr on every admin page counts as phoning home.
3. **Bundle remote assets locally (Guideline 8).** CDN-hosted JS/CSS, remote font files, third-party API clients pulling code from your server — all forbidden unless the resource is genuinely a service. Ship the file inside the ZIP.
4. **Source for every compiled file (Guideline 4).** Every webpack/vite/babel/sass output needs either bundled source or a public GitHub link in the readme. No mangled identifiers.
5. **Text domain == plugin slug, as a literal.** Every `__()`, `_e()`, `esc_html__()` etc. needs `'your-plugin-slug'` (no underscores, no variables, no constants).
6. **Escape on output.** Every shortcode return, block `render_callback`, `the_content` filter, admin notice — escape every dynamic part at the last moment with `esc_html` / `esc_attr` / `esc_url` / `wp_kses_post`.
7. **`permission_callback` on every REST route.** Never omit it, never set `null`. Use `__return_true` for intentionally public, `current_user_can( … )` for everything else.
8. **Don't `define()` core constants.** `ABSPATH`, `WPINC`, `WP_CONTENT_DIR` are core's. A plugin that redefines them gets flagged under "changing global behaviour".
9. **Use `plugin_dir_path( __FILE__ )` and friends, not `WP_PLUGIN_DIR . '/your-slug'`.** Users rename folders.
10. **Write to `wp_upload_dir()`, never to `plugin_dir_path()`.** Plugin folder is wiped on upgrade and public-readable.
11. **Don't force-deactivate other plugins.** Use WP 6.5+ Plugin Dependencies (`Requires Plugins:` header) instead of `deactivate_plugins( 'other-plugin/foo.php' )`.
12. **Prefix vendored PHP libraries.** Freemius, Guzzle, Monolog — anything in `vendor/` — must be prefixed (Strauss is the current recommendation) so it doesn't collide with another plugin's copy.

## The triage workflow

When you encounter plugin code, audit it in this order:

1. **Read the relevant reference file first** for the specific area you are touching. Don't try to remember rules — look them up.
2. **Run Plugin Check** (the official wp.org tool) before believing the code is clean: `wp plugin check <slug>` or via WP admin → Tools → Plugin Check. See `references/plugin-check-and-prefixing.md` for setup.
3. **Grep for known anti-patterns** before each commit. The reference files end with checklists — use them as grep targets:
   - `grep -rn "define.*ABSPATH" .` — should find zero non-comment hits
   - `grep -rn "WP_PLUGIN_URL.*'/" .` — should find zero
   - `grep -rn "__(\$" .` — variables in gettext calls
   - `grep -rn "deactivate_plugins" .` — should be empty (or only Freemius-vendored)
   - `grep -rn "include ABSPATH" .` — should be `require_once`, inside a callback
4. **For library conflicts** specifically (Freemius being the usual culprit), use Strauss — see `references/plugin-check-and-prefixing.md`.

## On reviewer mistakes

The closure emails from `plugins@wordpress.org` are partly machine-generated (marked `✨`). They will sometimes flag false positives. The reviewer's own guidance:

> "Note that there may be false positives — we are humans and make mistakes, we apologize if there is anything we have gotten wrong. If you have doubts you can ask us for clarification, when asking us please be clear, concise, direct and include an example."

That said, in practice it is almost always faster to **fix** a borderline flag than to argue it. Every back-and-forth round is days of waiting. Push back only when a fix would meaningfully regress the product, and when you do, reply with a concise paragraph + a code example.

## On replying to a closure thread

If the user is responding to an actual closure email:

1. Reply on the same thread (don't open a new submission).
2. Be concise. The Plugins Team review the full plugin again — you do not need to enumerate every change.
3. Include "the entire plugin is now in SVN trunk/ and tagged as <version>" as the operative statement.
4. Acknowledge their feedback briefly. Ask clarifying questions only if you genuinely cannot infer what they meant.
5. Do not paste blocks of code. They will read the SVN repo.

## On the SVN release

Even when the plugin is closed, you can still upload to SVN. The flow:

1. Bump `Version:` in the main plugin file's header.
2. Bump `Stable tag:` in `readme.txt`.
3. `svn co https://plugins.svn.wordpress.org/<slug>/`
4. Copy your built plugin into `trunk/`. Make sure your `.distignore` / build process excludes dev files (`src/`, `.github/`, `node_modules/`, `package.json` only-if-not-used-at-runtime, `.git/`, `tests/`, etc.).
5. `svn add` new files, `svn delete` removed ones.
6. `svn cp trunk tags/<version>` to create the tag.
7. `svn ci -m "Release <version>"` — the message can be terse; SVN log is not the user-facing changelog (readme is).
8. Reply on the HelpScout / email thread that the new version is up.

## Reference index

**wp.org directory & compliance:**
- [`references/guidelines.md`](references/guidelines.md) — All 19 numbered guidelines + the Guideline 4 deep dive for compiled/minified code
- [`references/i18n-and-escaping.md`](references/i18n-and-escaping.md) — Text domains, gettext rules, escape functions, shortcode/block/filter escaping, XSS vectors
- [`references/hooks-paths-uploads-rest.md`](references/hooks-paths-uploads-rest.md) — Actions/filters, plugin paths, Settings API, uploads dir, REST permission_callback
- [`references/plugin-check-and-prefixing.md`](references/plugin-check-and-prefixing.md) — Plugin Check setup + usage, library-prefixing with Strauss / Mozart / PHP-Scoper, Freemius prefixing recipe

**Plugin Developer Handbook (developer.wordpress.org/plugins/):**
- [`references/handbook-plugin-basics.md`](references/handbook-plugin-basics.md) — Plugin header fields, single-file vs folder, activation/deactivation/uninstall, path & URL functions, best practices
- [`references/handbook-security.md`](references/handbook-security.md) — Capabilities, validation, sanitizing input, escaping output, nonces; context→function tables; common vulns
- [`references/handbook-hooks-menus-shortcodes.md`](references/handbook-hooks-menus-shortcodes.md) — Actions vs filters, priorities, custom hooks, admin menus, shortcodes
- [`references/handbook-settings-data.md`](references/handbook-settings-data.md) — Options API, Settings API, post meta + meta boxes, custom post types, taxonomies
- [`references/handbook-privacy-users-http-cron.md`](references/handbook-privacy-users-http-cron.md) — Privacy/GDPR exporters & erasers, users/roles/caps, HTTP API, WP-Cron
- [`references/handbook-js-i18n-tools-directory.md`](references/handbook-js-i18n-tools-directory.md) — Enqueuing, jQuery, Ajax, internationalization, dev tools, readme.txt/assets/SVN

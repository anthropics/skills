# WordPress.org Plugin Directory Guidelines — Reference

Source: https://developer.wordpress.org/plugins/wordpress-org/detailed-plugin-guidelines/

Every numbered guideline the WordPress.org Plugin Directory imposes on plugin authors. Use this as a quick rules reference — always check the live page for the canonical, latest version, since the directory team reserves the right to amend guidelines at any time (see Guideline 18).

---

## Guideline 1 — GPL Compatibility

Every file shipped to the directory must be released under the GPL or a GPL-compatible license. That covers PHP, JS, CSS, images, fonts, data files, and any bundled third-party libraries. "GPLv2 or later" is the recommended choice because it matches WordPress core.

**Violation example:** Bundling a proprietary JS chart library whose license forbids redistribution, or an image released under a CC "non-commercial" license.

---

## Guideline 2 — Developer Responsibility

The author of a plugin is solely accountable for everything inside the ZIP, including third-party libraries, images, API usage, and adherence to external services' terms. Licensing of every dependency must be verifiable before submission; if you cannot confirm a license, you cannot ship the file. Deliberately working around guidelines, or re-adding code the review team asked you to drop, is itself a violation.

**Violation example:** Restoring an obfuscated tracker module that reviewers previously required to be removed, in a later release tag.

---

## Guideline 3 — Stable Version on the Directory

The build users actually receive is the one on WordPress.org. Authors who develop elsewhere (GitHub, a SaaS dashboard, etc.) must keep the directory copy current; treating the SVN repo as a stale mirror while distributing newer code through other channels can cause removal.

**Violation example:** Shipping v4.0 to paying users via a private update server while the WordPress.org directory still serves v2.1.

---

## Guideline 4 — Code Must Be (Mostly) Human Readable

Source must remain readable to future maintainers and reviewers. Tools and techniques whose effect is to obscure logic — packer-style obfuscation, uglify's name mangling, deliberately cryptic identifiers like `$z12sdf813d` — are disallowed. Obfuscation is treated as a common cover for malicious payloads, which is why the rule is strict. (See the dedicated deep-dive at the end of this file for the practical workflow this imposes on compiled plugins.)

**Violation example:** Shipping a JS file consisting of a single line of mangled, name-shortened code with no readable counterpart available.

---

## Guideline 5 — No Trialware

Plugins may not bundle features that are locked behind payment, a trial timer, or a usage quota, nor may they ship as sandbox-only API clients. All functionality contained in the plugin must be fully usable. Paid tiers belong in a separate add-on plugin distributed off WordPress.org, or in the remote service itself (see Guideline 6). Up-selling other paid products is fine within the limits of Guideline 11.

**Violation example:** A plugin whose export-to-CSV button shows "Upgrade to Pro to unlock" after 30 days of use. Or a plugin whose `get_player_id()` always returns player 1 unless a Pro license is detected.

---

## Guideline 6 — Software as a Service Is Permitted

A plugin may serve as a client for an external paid service (video hosting, transcription, AI, etc.). The remote service must offer genuine functionality, and its purpose and terms should be documented in the readme — a link to the Terms of Use is encouraged. What is not allowed: services whose only job is license-key validation, services manufactured by carving local code out of the plugin to fake a remote dependency, or plugins that are essentially storefronts for products bought elsewhere.

**Violation example:** A plugin that contains a working PDF generator locally but calls a remote endpoint solely to check whether the user paid this month.

---

## Guideline 7 — No User Tracking Without Consent

External calls that transmit any user, site, or usage data require explicit opt-in — typically a checkbox or a deliberate registration step. The readme should document what data is collected and why, ideally with a privacy policy link. Prohibited patterns include silent telemetry, deceptive consent flows, hotlinking unrelated remote assets, undocumented use of remote blocklists, and tracking ad networks. Genuine SaaS plugins are an exception: configuring an Akismet or Twitter-style integration is itself the consent.

**Violation example:** A plugin that pings `https://stats.example.com/collect` with site URL and admin email on every activation, with no setting to disable it.

---

## Guideline 8 — No Executable Code Through Third-Party Channels

Communication with documented remote services is fine, but the plugin itself must not run arbitrary code that comes from outside the directory. Specifically forbidden:

- Self-updating from a non-WordPress.org server
- Installing a "Pro" sibling plugin from elsewhere
- Loading non-font JS/CSS from third-party CDNs (host it locally)
- Pulling remotely curated lists where the service's terms don't allow it
- Wiring admin pages through iframes instead of real APIs

Remote management dashboards that push code from their own domain (not inside wp-admin) are permitted.

**Violation example:** A plugin that downloads `premium-features.php` from the vendor's S3 bucket and `include`s it at runtime. Or `wp_enqueue_script('chart', 'https://cdn.jsdelivr.net/npm/chart.js')`.

---

## Guideline 9 — No Illegal, Dishonest, or Offensive Conduct

A catch-all behavioural rule covering both the plugin's code and the author's conduct. Includes black-hat SEO and keyword stuffing, paid-traffic schemes, review manipulation (including sockpuppet accounts), pay-to-unlock messaging, plagiarising other authors, false claims of legal compliance (GDPR/ADA "guarantees"), abusing user server resources (crypto-mining, botnets), harassment of community members, identity falsification to evade prior sanctions, and deliberate loophole-hunting. Violations of the WordPress.org Community Code of Conduct, WordCamp Code of Conduct, and Forum Guidelines fall under this clause too.

**Violation example:** A plugin that uses idle browser cycles on the site's frontend to mine cryptocurrency for the developer.

---

## Guideline 10 — No Forced Front-End Credits or Links

"Powered by" badges, attribution links, and similar credits on the public site must be off by default and toggled on only by an informed, explicit user choice — not buried in a EULA. The plugin's core functionality cannot be gated on credits being visible. Remote services may brand their own output, but the branding has to live in the service's response, not in the plugin's PHP.

**Violation example:** A contact form plugin that prints "Form by Acme — get yours at acme.io" beneath every form unless the user finds a hidden constant to disable it.

---

## Guideline 11 — Don't Hijack the Admin Dashboard

Plugin UI should feel native to WordPress. Upgrade nags, promotional banners, and alerts should be scoped to the plugin's own settings screen or used very sparingly site-wide. Site-wide notices and dashboard widgets must be dismissible (or auto-dismiss when their condition clears). Error messages must explain the fix and remove themselves once fixed. Backend advertising is discouraged and is often a violation of the upstream ad network's own rules; tracking referral clicks via those ads is also blocked by Guideline 7. Linking to your own site or social channels is welcome.

**Violation example:** A persistent red banner on every admin page promoting the Pro version, with no dismiss control. Or a top-level admin menu placed at position 20 (next to Pages) "for visibility" instead of an unobtrusive slot.

---

## Guideline 12 — Readmes and Public Pages Must Not Spam

The readme, translation files, and other directory-facing text are written for human users, not for search engines. Spammy practices include affiliate links without disclosure, tagging competitors, using more than five tags, keyword stuffing, repeating the same tag, and any black-hat SEO. Affiliate links are allowed if disclosed and pointed directly at the partner (no cloaking or redirect URLs). A tag is acceptable only when the plugin genuinely extends that product — a WooCommerce extension may tag "woocommerce", but an Akismet alternative may not tag "akismet".

**Violation example:** A readme with `Tags: seo, yoast, rankmath, aioseo, seopress, allinoneseo` on a plugin that competes with Yoast.

---

## Guideline 13 — Use WordPress's Bundled Libraries

WordPress already ships jQuery, PHPMailer, SimplePie, PHPass, Atom Lib, and more. Plugins must use those bundled copies rather than including their own forks or different versions, which avoids version conflicts and keeps security patches centralised in core.

**Violation example:** Enqueuing your own `jquery-3.6.0.min.js` from the plugin's `assets/` directory instead of declaring `jquery` as a dependency in `wp_enqueue_script()`.

---

## Guideline 14 — Don't Commit Constantly

SVN on WordPress.org is a release channel, not a development branch. Every commit — even readme tweaks — regenerates the distributed ZIP. Push only when you're shipping (stable, beta, or RC). Tiny rapid-fire commits are treated as gaming the "Recently Updated" list. Write meaningful messages; avoid "update", "wip", "fix". The one acknowledged exception is a readme commit purely to bump "Tested up to" for a new WordPress release.

**Violation example:** Twelve commits in an hour, each labelled "typo", each touching one character of the readme.

---

## Guideline 15 — Increment the Version on Every Release

Update notices fire only when the version number changes. Trunk's `readme.txt` must always show the current version. Use SVN tags for releases and keep stable-tag pointers in sync. Releasing changes without a version bump means users will never receive the update.

**Violation example:** Pushing a security patch but leaving `Stable tag: 2.4.1` and `Version: 2.4.1` unchanged.

---

## Guideline 16 — Submit a Complete Plugin

Submissions are reviewed by humans inspecting an actual ZIP, so the plugin must be functional and finished at submission time. The directory does not reserve slugs for future builds or trademark holders; if you take a slug and never publish, it can be reassigned.

**Violation example:** Submitting an empty plugin scaffold to reserve the slug `super-cool-ai`.

---

## Guideline 17 — Respect Trademarks, Copyrights, and Project Names

A plugin slug cannot lead with a trademark or project name you don't represent. "WordPress" is a Foundation trademark and is blocked outright in slugs and domain names. If you don't own the brand, position it after a descriptor: `dancing-sloths-for-superbox`, not `super-sandbox-dancing-sloths`. The same applies to upstream projects you're integrating with — only the `mellowyellowsandbox.js` team can lead a slug with `mellowyellowsandbox`. Original branding is encouraged.

**Violation example:** A third-party developer publishing a plugin with the slug `woocommerce-shipping-extras`.

---

## Guideline 18 — Directory Maintenance Rights Reserved

The Plugins team reserves the right to:

- Update the guidelines whenever needed
- Remove or disable any plugin, even for reasons not listed here
- Grant exceptions and grace periods on a case-by-case basis
- Reassign a plugin to a new maintainer if the original goes inactive
- Patch a plugin without the author's consent when user safety requires it

The promise in return is that these powers are used sparingly and respectfully.

**Not really a violation a developer commits** — this is the meta-rule that explains why a removal can happen outside the strict letter of guidelines 1–17.

---

## Guideline 4 in Depth — Compiled, Minified, and Build-Tool Code

Guideline 4 is the rule that catches most modern JS/CSS workflows by surprise, so it deserves its own section. The directory page is briefer than the practice that the review team enforces, so the points below combine the literal rule with the operational expectations.

### What the rule literally says

- Obfuscation tools that hide intent — `packer`, uglify's mangle, and lookalikes — are not allowed.
- Cryptic identifiers (`$z12sdf813d`, single-letter variables across hundreds of lines) count as obscuring code.
- Developers must give the public maintained access to source code and build tools through one of two routes:
  1. Ship the source inside the deployed plugin, or
  2. Link from the readme to the development repo (GitHub, GitLab, Bitbucket, etc.) where the unminified source lives.
- The page strongly recommends documenting how the build tools are run.

### Minified JS and CSS

The page text does not literally use the word "minified" — its examples are obfuscation tools. In review practice, however, minified-only assets without an accompanying source are treated under the same rule: minification by itself is fine for performance, but the human-readable source must be reachable somewhere (either bundled in the ZIP or linked from the readme).

Safe pattern:
- `assets/js/foo.min.js` (shipped, minified)
- `assets/js/foo.js` (shipped, original) **or** `https://github.com/you/foo` linked from `readme.txt`

Unsafe pattern:
- Only `assets/js/foo.min.js` shipped, no source-mapped or unminified counterpart anywhere public.

### What counts as "compiled" code

The guideline page itself does not enumerate build tools by name. In practice the review team applies the rule to any pipeline that produces output that differs meaningfully from what a developer wrote, including:

- Webpack / Vite / Rollup / Parcel / esbuild bundles
- Babel / TypeScript / SWC transpilation output
- Sass / Less / PostCSS compiled stylesheets
- React/JSX builds (e.g. via `@wordpress/scripts`)
- Gulp or Grunt pipelines that minify, concatenate, or transform
- Composer-installed or npm-installed dependencies that ship as built artefacts

For each of those, the unprocessed source — `.jsx`, `.ts`, `.scss`, the webpack entry files, the `package.json` and `composer.json` — must be available either inside the deployed plugin or via the readme's development link.

### Readme expectations

- State where the source lives if it isn't bundled.
- Document the build command(s): which Node version, which `npm` script (`npm run build`, `gulp build`, etc.), what the output directory is.
- Document any environment requirements (Composer version, PHP version for build tooling, etc.).

A readme that just says "minified for performance" with no source link will typically be flagged.

### Exception language

Guideline 4 itself does not carry an explicit "unless…" clause. The room for judgement comes from Guideline 18's general right to grant exceptions case by case. In practice the reviewers focus on intent: a clearly named minified bundle with public source alongside it is fine, while mangled identifiers and missing source are not, regardless of the tool that produced them.

### Practical checklist for compiled plugins

1. Keep readable source for every shipped JS/CSS file — bundled in the ZIP or in a public repo linked from `readme.txt`.
2. Don't enable name-mangling/obfuscation in production builds; standard minification only.
3. Commit a `package.json` and/or `composer.json` so the build is reproducible.
4. Include a short "Building from source" or "Development" section in the readme: prerequisites, install command, build command, output paths.
5. When upstream dependencies ship only minified, document the upstream source URL in the readme so reviewers can verify it.

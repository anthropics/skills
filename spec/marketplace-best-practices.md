# Marketplace Best Practices

To keep your Claude Code marketplace clean and functional, follow these four best practices for organization and maintenance:

## 1. Structure as a Monorepo

Don't dump everything in the root. Use a dedicated plugins/ directory where each subfolder represents a standalone tool.

* Root: .claude-plugin/marketplace.json (The "Catalog").
* Subfolder: plugins/name/.claude-plugin/plugin.json (The "Identity").
* Isolation: Keep a skills/ folder inside each plugin folder to prevent command conflicts and allow users to install only what they need.

## 2. Explicit Path Mapping

In your root marketplace.json, always use explicit relative paths for the source field (e.g., "source": "./plugins/helper-tool"). Avoid using "source": "./" for multiple plugins, as this can cause Claude to misidentify which skills belong to which plugin.

## 3. Namespace Your Skills

To avoid "Command already exists" errors when users have multiple marketplaces installed:

* Unique Names: Ensure the name in plugin.json is unique (e.g., company-git-tools).
* Slug Consistency: Match your folder names to your plugin names to make debugging easier for your team.

## 4. Metadata Integrity

Every skill (the .md files) must have accurate YAML frontmatter.

* Required Fields: Every skill needs a name (kebab-case) and a clear description.
* Intent Matching: The description is what Claude uses to "understand" when to trigger the skill; make it specific to the plugin's purpose rather than generic.

Pro Tip: Set "strict": true in your marketplace.json if you want to ensure only explicitly listed skills are loaded, which prevents "ghost" or experimental files from appearing in the user's / menu.

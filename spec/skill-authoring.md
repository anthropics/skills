# Skill Authoring Guide

This guide describes how to create skills that agents can discover and use.

## Skill Folder Layout

A minimal skill folder looks like this:

```
my-skill/
  - SKILL.md
```

More complex skills can add additional directories and files as needed.


## The SKILL.md File

The skill's "entrypoint" is the `SKILL.md` file. It is the only file required to exist. The file must start with a YAML frontmatter followed by regular Markdown.

### YAML Frontmatter

The YAML frontmatter has 2 required properties:

- `name`
    - The name of the skill in hyphen-case
    - Restricted to lowercase Unicode alphanumeric + hyphen
    - Must match the name of the directory containing the SKILL.md
- `description`
    - Description of what the skill does and when Claude should use it

There are 3 optional properties:

- `license`
    - The license applied to the skill
    - We recommend keeping it short (either the name of a license or the name of a bundled license file)
- `allowed-tools`
    - A list of tools that are pre-approved to run
    - Currently only supported in Claude Code
- `metadata`
    - A map from string keys to string values
    - Clients can use this to store additional properties not defined by the Agent Skills Spec
    - We recommend making your key names reasonably unique to avoid accidental conflicts

### Markdown Body

The Markdown body has no restrictions on it.

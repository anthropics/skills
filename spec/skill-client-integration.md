# Skill Client Integration Guide

> [!IMPORTANT]
> This guide is intended for developers looking to add Skills support to a new agent or product.

There are two ways to integrate skills into your agent:

1. Filesystem-based
2. Tool-based

**Filesystem-based** Skill Clients have a computer environment (e.g., bash + unix) and are the most capable type of Skill Client since they can natively support skills that bundle scripts, code, and other resources. In this type of client, skills are "triggered" by the model issuing a shell command like `cat /path/to/my-skill/SKILL.md`. Similarly, when a skill refers to a bundled resource by relative path, the model uses shell commands to read or use the bundled asset.

**Tool-based** Skill Clients do not rely on a computer environment but instead define one or more tools that the model can use to trigger the skill and read or use bundled assets. The implementation details are left to the developer.

## Skill Installation

Skill installation depends on your agent architecture. For filesystem-based agents, a skill can be installed simply by copying the skill directory into the filesystem. For tool-based agents, the installation mechanism will depend on your specific architecture.

## Including Skills in the Agent's System Prompt

For the model to "trigger" a skill, it needs to know which skills are available. The progressive disclosure system starts by including a short list of information about each available skill in the context window (typically the system prompt). At a minimum, this must include the skill name and description. For filesystem-based Skill Clients, you must also include the absolute path to the skill's installed location.

The formatting of the list is up to you, but here is the format currently used at Anthropic:

```
<available_skills>
<skill>
<name>
my-skill
</name>
<description>
the skill's description
</description>
<location>
/path/to/my-skill/SKILL.md
</location>
</skill>
<skill>
...
</skill>
<skill>
...
</skill>
</available_skills>
```

The `<skill>` element repeats for each available skill.

**Fields**

- `name`
  - The name of the skill
  - Obtained from the `name` property in the SKILL.md file
- `description`
  - Describes what the skill does and when the model should consider using it
  - Obtained from the `description` property in the SKILL.md file
- `location`
  - The absolute filesystem path to the installed skill's SKILL.md file

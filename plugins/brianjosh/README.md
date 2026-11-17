# BrianJosh for OpenAI products

BrianJosh is authored by Dr. De.Souz.AI. This folder is a skill-only Agent Plugin for compatible ChatGPT and Codex installations. Its canonical instructions are in `skills/brianjosh/SKILL.md`; interview context is loaded from `skills/brianjosh/references/dr-de-souz-ai-source-notes.md` only when relevant. Brian Johnsrud and any past, current, or future employer did not create or endorse the skill.

## Codex installation

From a supported Codex CLI environment, add this repository as a marketplace:

```sh
codex plugin marketplace add mrdesouzaphd-cmyk/skills
```

Then install `brianjosh` from the `dr-desouz-ai-skills` marketplace in the Plugins Directory. The marketplace entry is in `../../.agents/plugins/marketplace.json` relative to this plugin folder.

## ChatGPT

The personal BrianJosh skill is separately installed in its creator's ChatGPT Skills directory. Repository publication alone does not install this plugin in other accounts or workspaces. Workspace or public directory publication follows OpenAI's plugin distribution and review flow.

## OpenAI API

The Responses API supports skills as uploaded bundles or inline skills, depending on the environment. Upload the `skills/brianjosh` folder as an API skill using an authorized API key and follow the current OpenAI Skills API documentation. The GitHub marketplace itself does not deploy an API skill or make the skill universal across products.

Source of installation details: https://developers.openai.com/plugins/build/plugins and https://developers.openai.com/api/docs/guides/tools-skills

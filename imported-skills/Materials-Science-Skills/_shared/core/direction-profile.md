# Direction Profile

Use profile-first routing for every `materials-*` skill.

## Local Profile

- Local file: `.materials/profile.yaml`
- This file is user-local and must not be committed.
- In the source repository, create or update it with `python scripts/materials_profile.py set "<user direction>"`.
- In the installed plugin package, the same helper is bundled at `plugins/materials-skills/scripts/materials_profile.py`.

## First Use

If `.materials/profile.yaml` is missing, ask the user once:

> What is your current materials research direction or application area? I will save it locally in `.materials/profile.yaml`; if it does not match an existing domain, I will use neutral/general materials support.

Then save the answer before choosing material-family or material-domain fragments.

## Later Use

If the profile exists, do not ask again. Briefly remind the user which saved direction is active, then continue. If the current request names a different direction, use the explicit request for this run but do not rewrite the profile unless the user asks to change it.

## Routing Order

1. Explicit direction in the current user request.
2. Saved `.materials/profile.yaml` values.
3. Neutral/general fallback.

Use `material_family: neutral` and `domain` or `material_domain: general` when no saved or explicit direction matches the skill's supported values. General routing loads broad materials assets and avoids assuming civil engineering by default.

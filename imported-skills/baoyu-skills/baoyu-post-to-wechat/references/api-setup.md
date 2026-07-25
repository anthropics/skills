# API Credential Setup

Guided setup when `WECHAT_APP_ID` / `WECHAT_APP_SECRET` are missing. Invoked by Step 2 of the article-posting workflow.

## Detection

Look for the credentials in this order:

1. Env vars `WECHAT_APP_ID` / `WECHAT_APP_SECRET`
2. `<cwd>/.baoyu-skills/.env` with `WECHAT_APP_ID=...`
3. `$HOME/.baoyu-skills/.env` with `WECHAT_APP_ID=...`

If none are present, run the guided setup below.

## Guided Setup

Show this message to the user and ask where to save:

```
WeChat API credentials not found.

To obtain credentials:
1. Visit https://mp.weixin.qq.com
2. Go to: 开发 → 基本配置
3. Copy AppID and AppSecret

Where to save?
A) Project-level: .baoyu-skills/.env (this project only)
B) User-level: ~/.baoyu-skills/.env (all projects)
```

After they choose a location, collect the values (prefer a user-input tool, fall back to a numbered prompt per the User Input Tools rule in SKILL.md) and append:

```
WECHAT_APP_ID=<user_input>
WECHAT_APP_SECRET=<user_input>
```

## Multi-Account Variant

If the user has multiple accounts configured (`accounts:` block in EXTEND.md), use prefixed keys instead — see `multi-account.md` → "Credential Resolution".

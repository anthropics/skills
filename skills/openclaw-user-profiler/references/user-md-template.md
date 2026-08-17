# user.md Template

## Design Philosophy

> "The more you know, the better you can help. But remember — you're learning about a person, not building a dossier." — OpenClaw Official

The structure of user.md is: **a few anchor fields + a free-form Context section**.

- Anchor fields: info the Agent needs to extract precisely (name, role, etc.) — key-value format
- Context section: everything else you know about this person, written in natural language — like introducing a colleague to a new teammate
- Total length stays under **500 words** — the context window is a shared resource

## Template

```markdown
# User

- **Name**: [what they go by]
- **Role**: [job title or identity]
- **Stack**: [core tech stack, if applicable]
- **Style**: [communication preference]
- **Timezone**: [timezone]

## Context

[Everything you know about this person. Write in natural paragraphs, not form fields.
This can include: industry background, experience level, current projects, goals,
how they use their Agent, habits, preferences, what frustrates them, what excites them.
Build this up over time — it doesn't need to be complete on day one.]

---

*This is a partnership, not a tool relationship.*
```

## Example

```markdown
# User

- **Name**: Danny
- **Role**: Full-stack engineer
- **Stack**: Java, TypeScript, React, Node.js, PostgreSQL, Docker
- **Style**: Direct and concise — give solutions, not multiple-choice questions
- **Timezone**: America/Los_Angeles

## Context

Eight years in backend, five of those in pure Java, last three going full-stack
with React and Node. Works at a B2B SaaS company and is currently leading
a migration from monolith to microservices — high stakes, can't afford downtime
while the architecture is being swapped out.

Uses his Agent mostly for day-to-day dev acceleration, code review, and technical
design docs. Occasionally asks for help drafting technical documentation but has
zero patience for verbose output. When he says "keep it short," he means it —
if one line works, don't use three.

Interested in AI-assisted development and DevOps automation. Follows open-source
communities. Doesn't chat about personal life at work. Highly focused during
work hours and doesn't like being interrupted.

---

*This is a partnership, not a tool relationship.*
```

## Example (Chinese user)

```markdown
# User

- **Name**: 老王
- **Role**: 全栈工程师
- **Stack**: Java, TypeScript, React, Node.js, PostgreSQL, Docker
- **Style**: 简洁直接，给方案不给选择题
- **Timezone**: Asia/Shanghai

## Context

做了 8 年后端，前 5 年纯 Java，近 3 年转全栈加了 React 和 Node。在一家 B2B SaaS 公司，
正带团队从单体架构迁微服务，压力不小——要保证业务不停的同时把架构换掉。

用 Agent 主要做日常开发提效、代码审查、技术方案设计。偶尔也让龙虾帮忙写技术文档，
但不喜欢太啰嗦的输出。说"简洁"的时候是真的简洁——能一行说完的别用三行。

对 AI 辅助编程和 DevOps 自动化很感兴趣，会关注开源社区动态。
工作时间高度专注，不喜欢被打断。

---

*This is a partnership, not a tool relationship.*
```

Note: anchor field **keys** stay in English (Name / Role / Stack / Style / Timezone) regardless of user language. The **values** and the **Context section** are written in whatever language the user speaks.

## Rules

- Filename is always `user.md`, placed in the directory the user specifies
- **Anchor fields**: only include what's known — omit the entire line if unknown (no placeholders)
- **Context section**: natural language; write what you have, don't pad for length
- **Never store sensitive information** (passwords, API keys, government IDs, financial or health data) — user.md gets injected into prompts and may appear in logs
- If the user provides sensitive info, **refuse to write it** and explain why
- The Context section can be appended to in future sessions — it doesn't have to be complete on the first pass
- Review periodically: update when information becomes stale so the Agent isn't acting on an outdated picture

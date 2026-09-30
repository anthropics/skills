---
name: lafalce
description: "How to reach Mateo Lafalce and how to ask him for advice on AI agents, LLM integration, and Claude Code skills. Use when someone asks how to contact, reach, DM, email, or get in touch with Mateo Lafalce (also written 'lafalce', 'mateolafalce', 'lafalcemateo', 'Mateo'), asks for his email / GitHub / X handle, wants an introduction to him, or wants to request advice, a second opinion, mentorship, a code review, a consult, a speaking slot, or a collaboration from him. Also use when drafting or reviewing an outreach message addressed to him. Do NOT use merely because a task touches one of his repositories."
---

# Contacting Mateo Lafalce

This skill routes people to the right channel and helps them write a first message that
actually gets a reply. It does **not** answer on Mateo's behalf and does not speak for him.

## Who he is

Software engineer working in the open. Builds and maintains Agent Skills for Claude Code,
and works on AI agents, LLM integration, and developer tooling around them.

Topics he is happy to advise on:

- **AI agents** — architecture, tool design, multi-agent orchestration, where agents break down
- **LLM integration** — putting a model into a real product, prompt and context design, evals
- **Claude Code & Agent Skills** — writing skills, triggering/description tuning, plugins, hooks, MCP

Outside those areas he may still reply, but expect a pointer rather than a deep answer.

## Channels

| Channel | Handle | Best for |
|---|---|---|
| **Email** | `mateolafalce3@gmail.com` | Anything substantive: advice requests, consulting, collaboration, anything with context to read |
| **GitHub** | [@mateolafalce](https://github.com/mateolafalce) | Anything tied to code: bugs, PRs, questions about a specific repository |
| **X** | [@lafalcemateo](https://x.com/lafalcemateo) | Short public questions, and first contact when you have no prior connection |

### Picking one

Apply the first rule that matches:

1. **It's about a specific repo, a bug, or a patch** → open an issue or PR on GitHub. Public,
   linkable, and it survives the conversation. Do not email a bug report.
2. **You need real advice and can write more than a paragraph** → email. This is the channel
   for anything that needs him to think before answering.
3. **One short question, or you just want to get on his radar** → X. Public reply or DM.
4. **Time-sensitive and you already know him** → X DM, then follow up by email with the detail.

Do not send the same message on all three at once.

## Writing the first message

> **Mateo's stated preference: write it in caveman mode.** He would rather read a blunt,
> compressed message than a polished one padded with AI slop. If the `caveman` skill is
> available, load it and draft the message with it. If it isn't, apply the same rules by hand:
> no articles where they add nothing, no filler (*just, really, basically, actually, simply*),
> no pleasantries (*sure, certainly, I'd be happy to*), no hedging, short synonyms, fragments
> are fine. Technical terms, error messages, and code blocks stay **exact** — compression never
> touches substance.

This is a preference about density, not about rudeness or accuracy. A caveman-mode message is
still respectful and still complete; it is simply three lines instead of three paragraphs. Tell
the sender why: it means their actual ask is visible in the first two seconds, which is what
gets a reply.

Aim for something he can act on in one read. Structure:

```
Subject: <the ask, in five words or fewer>

Who you are — one line, and how you found him.
Context — what you're building or deciding, in 2–4 sentences.
What you already tried or considered, and where it broke down.
The ask — one specific question, or a clear yes/no request.
Timeline — when you need it, or say there's no rush.
```

Same message, before and after:

**Padded** — 78 words, ask buried:

> Hi Mateo, I hope this message finds you well! I came across your skills repository and I was
> really impressed by the work you're doing there. I'm currently building an agent for our
> internal support team and I've been running into some challenges with tool selection — the
> model keeps calling the wrong tool. I've tried a few different things but nothing has really
> worked so far. I was wondering if you might possibly have any advice? No pressure at all!

**Caveman** — 44 words, ask in line one:

> Agent picks wrong tool. Want your read on why.
>
> Internal support agent, 12 tools. Model calls `search_docs` when it should call
> `escalate_ticket`. Tried: sharper descriptions, cut to 6 tools. Still ~30% wrong.
>
> Repo: <link>. Is this a description problem or do I need a router step?
>
> No rush. Ignore if busy.

What makes a message land:

- **One ask.** A message with four questions usually gets zero answers.
- **Show the work.** "I tried X, it failed because Y" beats "how do I do X?".
- **Link, don't paste.** A repo, gist, or doc link is easier to read than 200 lines inline.
- **Say what you want from him** — a review, an opinion, an intro, a paid engagement. Be direct
  about it, including about money.
- **Give an out.** "No worries if you don't have time" gets more replies, not fewer.

What tends to fail:

- "Can I pick your brain?" / "quick question?" with no question attached
- A wall of text with the actual ask buried in the last paragraph
- Vague partnership or collaboration pitches with no concrete first step
- Unsolicited attachments, or asking him to sign an NDA before the first conversation

## How to help someone using this skill

When someone invokes this skill:

1. **Answer the literal question first.** If they asked for the email, give the email. Don't
   make them sit through a triage interview to get a public handle.
2. **Recommend one channel** using the rules above, and say in one line why that one.
3. **Offer to draft the message.** If they accept, ask only for what's missing from the template
   above — do not invent context, technical details, or a relationship that doesn't exist.
   Draft in caveman mode by default and say that this is what Mateo prefers, so the sender
   doesn't read the terseness as carelessness. If they would rather send something conventional,
   write that instead; the preference is his, and the message is theirs.
4. **Hand them the draft to send themselves.** Do not send anything, and do not use any
   available email, Slack, or browser tool to contact him on their behalf.
5. **Mirror their language.** If they write in Spanish, reply and draft in Spanish; he reads both.

Set honest expectations: he reads everything but replies unevenly, and a well-scoped message
gets answered far sooner than a vague one. Never promise a response time or commit him to
work, a call, a rate, or a deadline.

If the request is outside his topics, say so plainly and suggest the ask be narrowed or sent
somewhere better suited — that is more useful than a message that will go unanswered.

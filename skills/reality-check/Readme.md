# RealityCheck
### Your Idea vs The Real World

> "The more confident you sound, the harder it goes."

Most people validate their ideas by talking to friends who say it sounds great.  
RealityCheck does the opposite — it interviews you, researches the space, and tells you the truth.

---

## What It Does

RealityCheck is a Claude AI skill that runs your idea through 3 phases:

```
Phase 1: Interview  ->  Phase 2: Research  ->  Phase 3: Critique + Verdict
```

---

## The Three Phases

### Phase 1 — The Interview

Claude asks questions in smart batches covering your idea, the market, the competition, your unfair advantage, and how you plan to build it. It keeps going until it has a complete picture.

One thing happens quietly in the background: it tracks how overconfident you sound. The more certain you are that your idea will work, the harsher Phase 3 becomes.

### Phase 2 — Deep Research

Once the interview is done, Claude goes off and researches the space on its own. No prompting needed.

| Source | What It Looks For |
|--------|-------------------|
| General Web | Market landscape, existing solutions, recent news |
| News | Is this space growing or dying? Who just got funded or shut down? |
| Academic / Reports | Market size data, technical feasibility, industry studies |
| Reddit / Forums | Real user complaints, community skepticism, lived experience |
| YouTube | Product demos, expert breakdowns, community consensus |

It runs between 6 and 15 searches adaptively — stops when it's confident it has enough to give you a real answer.

### Phase 3 — Critique + Verdict

This is where it gets honest.

**Scorecard** — 8 dimensions rated out of 10, each with evidence-backed justification:

| Dimension | What Gets Evaluated |
|-----------|-------------------|
| Problem Clarity | Is the problem real, specific, and painful enough? |
| Market Size | Is there enough of a market to matter? |
| Solution Differentiation | Is this meaningfully better than what exists? |
| Technical Feasibility | Can this actually be built, and at what cost? |
| Business Model Viability | Can it make money? Are the unit economics sane? |
| Founder-Market Fit | Are you the right person to build this? |
| Timing | Is now the right moment, or too early/late? |
| Adoption Likelihood | Will real people actually use or pay for this? |

**Deep Analysis** — Covers what is genuinely strong, technical risks, economic risks, adoption risks, competitive threats, and an Assumption Graveyard listing the beliefs you are treating as facts but have not yet proven.

**Verdict** — One sentence. Build it, pivot it, or kill it — and why.

**Fix List** — For every major weakness, one concrete action you can take in the next 30 days, with a measurable signal to know if it worked.

---

## Harshness Levels

RealityCheck adapts its tone based on what it detects during the interview.

| Confidence Level Detected | Critique Style |
|--------------------------|----------------|
| Low — you acknowledge risks and unknowns | Balanced and constructive |
| Medium — mostly positive, some blind spots | Direct, assumptions challenged clearly |
| High — certain it will work, dismissive of risk | VC rejection mode, every claim questioned |

---

## What Kinds of Ideas Work

Anything you would ask "should I build this?" about:

- Startup and SaaS ideas
- Physical or digital products
- Mobile or web apps
- Business and service models
- Inventions and hardware
- Growth strategies and plans
- Creative projects and communities

---

## Installation

1. Download `reality-check.skill`
2. Go to Settings in Claude
3. Open the Skills tab
4. Upload the file
5. Start a conversation and describe your idea

Once installed, it triggers automatically whenever you say things like "I have an idea", "reality check this", "is this viable", "should I build X", or "roast my idea".

---

## Why It Exists

Most idea validation frameworks ask you to fill out a canvas or answer a checklist yourself. The problem is that you already believe in your idea — so you answer every question optimistically.

RealityCheck flips this. It asks the questions, finds the evidence, and stress-tests your assumptions so you find out what is actually true before you spend months building something the market does not want.

---

## Built With

- Claude AI (Anthropic)
- Claude Skills framework
- Web search across general, news, academic, Reddit, and YouTube sources

---

*Built as a personal Claude skill. Free to use and modify.*
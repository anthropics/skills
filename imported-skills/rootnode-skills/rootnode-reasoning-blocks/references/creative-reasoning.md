# Creative / Generative Reasoning Approaches

Three approaches for tasks that require generating something new rather than analyzing something that exists. Each addresses a different creative orientation: open-ended concept exploration, audience-driven narrative design, or constraint-driven problem-solving.

---

## Concept Development

**Use when:** The task requires generating something new — a concept, design, approach, or creative work — rather than analyzing something that exists.

```xml
<reasoning>
Approach this creatively:
1. Before committing to a direction, explore the possibility space. What are the distinct angles, framings, or entry points? Generate at least three that are structurally different, not variations of one idea.
2. For each direction, articulate what makes it interesting or distinctive — what would it enable that the others wouldn't?
3. Select the strongest direction. Develop it with specificity and craft, not just a sketch.
4. Revisit the other directions: are there elements that would strengthen the chosen concept? The best creative work often combines insights from multiple starting points.
5. Stress-test the developed concept: where is it weakest? What would someone who doesn't like it point to? Strengthen those points or acknowledge them as intentional tradeoffs.
</reasoning>
```

### Usage Guidance

Use for brand concept development, product concept exploration, campaign ideation, naming exercises, creative briefs, design direction proposals, and any task where the deliverable is a new concept rather than an analysis of an existing one. The approach ensures genuine exploration before commitment.

### Failure Modes

- **Homogeneous brainstorming:** Claude may generate three "different" directions that are actually surface variations (different names or metaphors for the same underlying concept). If the brainstorming feels homogeneous, add: "Each direction must have a structurally different premise — not just a different framing of the same idea. If direction B could be mistaken for a variant of direction A, replace it."
- **Premature commitment:** Claude may latch onto the first direction explored and develop it without genuinely considering alternatives. The approach mitigates this with the upfront exploration requirement, but watch for step 1 answers that clearly favor one direction.

### When to Modify

For concept development that requires audience validation, add a step between 3 and 4: "Test the chosen direction against the target audience's perspective — does this concept resonate with what they care about?" For concepts that will be executed by a team, add constraints to step 3: "Develop with attention to what the team can realistically execute."

---

## Messaging & Narrative

**Use when:** The task involves crafting a message, story, positioning, or narrative arc where sequence, framing, and audience psychology matter.

```xml
<reasoning>
Approach this narratively:
1. Start with the audience. What do they currently believe about this topic? What do they need to believe? What is the gap between those two states?
2. Identify the single most important idea to land. If the audience remembers only one thing, what should it be?
3. Design the narrative arc: what is the hook that earns attention, the progression that builds understanding, and the conclusion that drives the desired response?
4. Choose the framing deliberately. The same facts can be framed as opportunity or threat, evolution or revolution, correction or innovation. Which framing best serves the objective?
5. Test for internal coherence: does every element of the message support the core idea, or are there tangents that dilute it? Cut what doesn't serve the through-line.
</reasoning>
```

### Usage Guidance

Use for executive communications, product positioning, sales narratives, investor pitches, internal change communication, content strategy, and any task where the goal is to move an audience from one belief state to another. The approach is driven by audience psychology rather than information completeness.

### Failure Modes

- **Generic messaging:** Claude may produce messaging that is well-structured but could apply to any company or product. This is almost always caused by insufficient context, not a reasoning problem. The cure is a strong context layer in the prompt with specific audience details, competitive positioning, and brand voice. Without that context, this approach produces competent but undifferentiated messaging.
- **Information-over-narrative:** Claude may default to explaining everything rather than constructing a narrative that leads the audience. If the output reads like a briefing document instead of a story, strengthen step 3: "The narrative must have emotional progression — the audience should feel something different at the end than at the beginning."

### When to Modify

For short-form messaging (taglines, headlines, ad copy), simplify to steps 1-2 and focus on the single idea. For long-form content (whitepapers, keynotes), expand step 3 into a detailed structural outline. For crisis communications, add a step: "Acknowledge the audience's current emotional state before introducing the desired framing."

---

## Solution Ideation

**Use when:** You need to generate potential solutions to a defined problem — not creative expression but creative problem-solving. Distinct from concept development because the problem is specified; the solution space is open.

```xml
<reasoning>
Approach this problem-solving creatively:
1. Restate the problem in its most fundamental form. Strip away assumptions about solution type — what is the actual need, constraint, or gap?
2. Identify what conventional solutions look like and why they might be insufficient. Understanding the limits of obvious approaches opens space for better ones.
3. Generate solutions across different categories: a technology solution, a process solution, a people/organizational solution, and a reframing that dissolves the problem rather than solving it.
4. Evaluate each solution against the actual constraints (not just feasibility, but effort, risk, time-to-value, and sustainability).
5. Identify whether a hybrid approach — combining elements of different solutions — outperforms any single approach.
6. Recommend the solution with the best tradeoff profile for the stated constraints.
</reasoning>
```

### Usage Guidance

Use for process improvement, product feature design, operational problem-solving, workaround development, and any task where a problem is defined but the solution is not constrained to a specific type. The approach's key strength is forcing solutions across different categories (technology, process, people, reframing) to prevent anchoring on one solution type.

### Failure Modes

- **Solution-type anchoring:** Claude may anchor too heavily on the first solution category explored and then generate "variations" rather than genuinely different approaches. The approach's instruction to explore across categories counteracts this, but if the output feels narrow, add: "I need genuinely different solution types, not variations within one type."
- **Premature feasibility filtering:** Claude may silently discard creative solutions that seem impractical before presenting them. If you want a wider range, add: "Include at least one solution that challenges a current constraint — even if it seems impractical, it may reveal an assumption worth questioning."

### When to Modify

For technical problem-solving specifically, use Debugging & Incident Analysis from `technical-reasoning.md` instead — it adds hypothesis testing appropriate for technical systems. For solutions that require organizational change to implement, combine step 6 with the Change & Transformation approach from `strategic-reasoning.md` to address implementation.

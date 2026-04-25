# AI UX Pattern Library Reference

Source: [aiuxdesign.guide](https://aiuxdesign.guide) — 36 patterns from 50+ shipped products

When a user describes behavior that matches a pattern below, name it naturally in conversation, explain what makes their implementation specific, and include the pattern URL in the gist.design file.

Only reference patterns when the user's description genuinely matches. Don't force patterns where none exist.

---

## Human-AI Collaboration

### Contextual Assistance

Offer timely, proactive help based on user context, history, and needs.

- URL: https://aiuxdesign.guide/patterns/contextual-assistance
- Used by: GitHub, Google, Notion
- Look for: Help that appears based on what the user is doing, not just what they ask for

### Human-in-the-Loop

Balance automation with human oversight for critical decisions.

- URL: https://aiuxdesign.guide/patterns/human-in-the-loop
- Used by: Google, Grammarly, OpenAI
- Look for: Any flow where AI suggests but the human decides — editing, approving, reviewing, overriding
- Common variants: Direct editing (low friction), accept/reject chips (medium), review queue (high friction)

### Augmented Creation

Empower users to create content with AI as a collaborative partner.

- URL: https://aiuxdesign.guide/patterns/augmented-creation
- Used by: Figma, GitHub Copilot, Midjourney
- Look for: AI that assists creation rather than replacing it — drafts, suggestions, variations

### Collaborative AI

Enable effective collaboration between multiple users and AI within shared workflows.

- URL: https://aiuxdesign.guide/patterns/collaborative-ai
- Used by: Notion, Slack
- Look for: AI operating within team contexts, shared outputs, multi-user awareness

### Feedback Loops

User corrections and preferences improve AI performance over time.

- URL: https://aiuxdesign.guide/patterns/feedback-loops
- Used by: ChatGPT, Claude
- Look for: Thumbs up/down, corrections that train the model, preference learning

### Graceful Handoff

Seamless transitions between AI automation and human control.

- URL: https://aiuxdesign.guide/patterns/graceful-handoff
- Used by: Adobe, Tesla
- Look for: Moments where the system transfers control to a human or vice versa

### Autonomy Spectrum

Provide a range of autonomy levels — from passive suggestions to full autonomy — that users can adjust per task type.

- URL: https://aiuxdesign.guide/patterns/autonomy-spectrum
- Used by: GitHub, Microsoft, Notion
- Look for: Settings or controls that let users decide how independently the AI operates. Sliders between "suggest only" and "do it for me." Per-task autonomy levels.
- Agentic pattern

### Intent Preview

Before any significant action, the agent presents a clear summary of what it intends to do — showing planned steps, reversibility status, and edit controls.

- URL: https://aiuxdesign.guide/patterns/intent-preview
- Used by: Claude, GitHub
- Look for: "Here's what I'm about to do" confirmations before agents execute. Plan approval flows. Step-by-step previews with edit/cancel options.
- Agentic pattern

### Escalation Pathways

Structured triggers and handoff mechanisms so agents pause and ask for human guidance when they hit ambiguity, conflicts, or decisions beyond their authorization.

- URL: https://aiuxdesign.guide/patterns/escalation-pathways
- Look for: Agent asking "I'm not sure about this — should I proceed?" Defined boundaries where the agent stops and defers. Escalation to human without losing context.
- Agentic pattern

### Mixed-Initiative Control

Interaction models where control flows seamlessly between human and agent — supporting parallel work, interruptible agent activity, and natural handoffs.

- URL: https://aiuxdesign.guide/patterns/mixed-initiative-control
- Used by: ChatGPT, Figma
- Look for: Human and AI working on the same thing simultaneously. User can interrupt or redirect the agent mid-task. No formal "take over" action required.
- Agentic pattern

---

## Trustworthy & Reliable AI

### Explainable AI (XAI)

Make AI decisions understandable via visualizations, explanations, and transparent reasoning.

- URL: https://aiuxdesign.guide/patterns/explainable-ai
- Used by: Claude, Hugging Face, Perplexity
- Look for: Citations, reasoning chains, "why did AI do this?" affordances

### Confidence Visualization

Display AI certainty levels through visual indicators.

- URL: https://aiuxdesign.guide/patterns/confidence-visualization
- Used by: AWS, GPTZero
- Look for: Confidence scores, certainty badges, reliability indicators

### Error Recovery & Graceful Degradation

Fail gracefully with clear recovery paths when things go wrong.

- URL: https://aiuxdesign.guide/patterns/error-recovery
- Used by: ChatGPT, GitHub, Grammarly
- Look for: Fallback states, retry mechanisms, manual overrides when AI fails

### Responsible AI Design

Prioritize fairness, transparency, and accountability throughout the AI lifecycle.

- URL: https://aiuxdesign.guide/patterns/responsible-ai-design
- Used by: Hugging Face, IBM, Microsoft
- Look for: Bias mitigation, model cards, ethical guardrails

### Safe Exploration

Provide sandbox environments for experimenting with AI without risk.

- URL: https://aiuxdesign.guide/patterns/safe-exploration
- Used by: GitHub, OpenAI, Photoshop
- Look for: Preview modes, undo/revert, "try without committing" flows

### Plan Summary

A structured breakdown of the agent's reasoning and approach — showing goal interpretation, strategy, subtask checklist, and assumptions — before execution begins.

- URL: https://aiuxdesign.guide/patterns/plan-summary
- Used by: ChatGPT, Claude, Devin
- Look for: Agent showing its plan before acting. Numbered steps with checkboxes. "Here's how I'll approach this" breakdowns. Assumption surfacing.
- Agentic pattern

### Action Audit Trail

A timestamped, structured log of every action the agent took — grouped by task, with reversibility status, selective undo, and diff views.

- URL: https://aiuxdesign.guide/patterns/action-audit-trail
- Used by: Claude, GitHub
- Look for: Logs of what the agent did and when. Undo buttons per action. Diff views showing before/after. "What changed?" summaries.
- Agentic pattern

### Trust Calibration

Progressively build appropriate trust through demonstrated competence — showing track records per domain, celebrating milestones, and adjusting oversight based on actual performance.

- URL: https://aiuxdesign.guide/patterns/trust-calibration
- Used by: GitHub, Gmail, Spotify
- Look for: "This agent has completed 47 tasks with 95% accuracy." Progressive permission unlocking. Earned autonomy based on track record. Domain-specific trust levels.
- Agentic pattern

---

## Natural Interaction

### Progressive Disclosure

Gradually reveal information, options, or AI features to reduce cognitive load.

- URL: https://aiuxdesign.guide/patterns/progressive-disclosure
- Used by: Google, Loom
- Look for: Features hidden behind "show more", wizards, staged onboarding

### Conversational UI

Design intuitive, human-like interactions via chat and voice interfaces.

- URL: https://aiuxdesign.guide/patterns/conversational-ui
- Used by: Microsoft, Siri, Slack
- Look for: Chat interfaces, voice input, natural language commands

### Multimodal Interaction

Combine voice, touch, gesture, text, and visual input for natural interaction.

- URL: https://aiuxdesign.guide/patterns/multimodal-interaction
- Used by: Google, Tesla
- Look for: Multiple input types working together — voice + touch, image + text

### Context Switching

Smooth transitions between tasks or topics while maintaining continuity.

- URL: https://aiuxdesign.guide/patterns/context-switching
- Used by: ChatGPT, Notion
- Look for: Conversation threads, task history, "pick up where you left off"

---

## Adaptive & Intelligent Systems

### Adaptive Interfaces

Interfaces that learn user behavior and adjust layout and functionality.

- URL: https://aiuxdesign.guide/patterns/adaptive-interfaces
- Used by: Duolingo, Netflix, Spotify
- Look for: Personalized layouts, reordered features, "for you" sections

### Guided Learning

Break complex tasks into guided steps, adapting to user knowledge levels.

- URL: https://aiuxdesign.guide/patterns/guided-learning
- Used by: Figma, GitHub
- Look for: Tutorials that adapt, progressive skill building, contextual education

### Ambient Intelligence

Unobtrusive AI that senses context and assists without explicit interaction.

- URL: https://aiuxdesign.guide/patterns/ambient-intelligence
- Used by: Apple, Google, Tesla
- Look for: Background automation, smart defaults, environment-aware behavior

### Predictive Anticipation

AI that predicts user needs before they're expressed.

- URL: https://aiuxdesign.guide/patterns/predictive-anticipation
- Used by: Netflix, Spotify
- Look for: Pre-loaded content, suggested next actions, "you might want" prompts

---

## Performance & Efficiency

### Intelligent Caching

Pre-fetch and cache AI content for instant results, reducing latency.

- URL: https://aiuxdesign.guide/patterns/intelligent-caching
- Used by: GitHub, Midjourney
- Look for: Pre-computed results, warm caches, instant suggestions

### Progressive Enhancement

Provide immediate basic responses then progressively add detail and accuracy.

- URL: https://aiuxdesign.guide/patterns/progressive-enhancement
- Used by: Claude, DALL-E, Perplexity
- Look for: Streaming responses, low-res to high-res, skeleton states that fill in

### Agent Status & Monitoring

A layered status system with escalating attention demands — from ambient badges to glanceable progress panels to interrupting notifications.

- URL: https://aiuxdesign.guide/patterns/agent-status-monitoring
- Used by: ChatGPT, Devin
- Look for: Progress bars for agent tasks. "Working on step 3 of 7" indicators. Background task badges. Notification when agent needs attention vs just showing completion.
- Agentic pattern

---

## Privacy & Control

### Privacy-First Design

Minimize data collection and provide transparent privacy controls.

- URL: https://aiuxdesign.guide/patterns/privacy-first-design
- Used by: DuckDuckGo
- Look for: Data minimization, on-device processing, clear data policies

### Selective Memory

Control what AI remembers, forgets, or ignores with transparent settings.

- URL: https://aiuxdesign.guide/patterns/selective-memory
- Used by: Anthropic, ChatGPT
- Look for: Memory controls, "forget this", conversation scope settings

---

## Accessibility & Inclusion

### Universal Access Patterns

Ensure equitable access for all abilities, languages, and assistive technologies.

- URL: https://aiuxdesign.guide/patterns/universal-access-patterns
- Used by: Be My Eyes, Microsoft
- Look for: Screen reader support, alternative input methods, language accessibility

---

## Safety & Harm Prevention

### Crisis Detection & Escalation

Detect crisis signals and immediately provide professional resources.

- URL: https://aiuxdesign.guide/patterns/crisis-detection-escalation
- Used by: ChatGPT, Crisis Text Line, Woebot
- Look for: Safety triggers, escalation paths, professional resource handoffs

### Session Degradation Prevention

Maintain AI quality and safety across extended interactions.

- URL: https://aiuxdesign.guide/patterns/session-degradation-prevention
- Used by: Wysa
- Look for: Context window management, quality maintenance over long sessions, session limits

### Anti-Manipulation Safeguards

Detect actual harmful intent beyond surface framing, regardless of how it's disguised.

- URL: https://aiuxdesign.guide/patterns/anti-manipulation-safeguards
- Used by: Bing, ChatGPT, Claude
- Look for: Jailbreak resistance, prompt injection handling, detecting harmful requests wrapped in legitimate framing ("for research purposes")

### Vulnerable User Protection

Detect vulnerable users and apply graduated age, crisis, and dependency protections.

- URL: https://aiuxdesign.guide/patterns/vulnerable-user-protection
- Used by: Woebot
- Look for: Age-appropriate content filtering, dependency detection (user treating AI as sole companion), graduated safety responses based on vulnerability signals

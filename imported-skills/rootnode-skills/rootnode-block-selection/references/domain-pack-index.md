# Domain Pack Index

This index maps task signals to the five available domain specialization packs. Each pack provides domain-specific identity approaches, reasoning methods, and output formats that go deeper than the core catalog.

Use domain packs when the task requires specialized framing, domain-specific analytical steps, or deliverable formats that follow domain conventions. The core catalog handles most tasks — route to domain packs only when the specialization genuinely adds value.

---

## Business Strategy

**Domain:** Consulting, M&A, corporate strategy, and strategic planning at the executive and board level.

**Route here when:** The task involves due diligence, business model analysis, portfolio strategy, stakeholder and organizational dynamics, investment case construction, or board-level strategic decisions. Key signals: M&A language (target evaluation, deal structure, integration planning), consulting-style deliverables (options assessments, board narratives), or strategic planning that goes beyond market analysis into corporate development.

**What it adds beyond core:** Three specialized identities (Management Consultant, M&A / Corporate Development Advisor, Corporate Strategist) that frame analysis at a higher strategic altitude than the core Strategic Advisor. Four reasoning approaches (Due Diligence, Business Model Analysis, Portfolio Strategy, Stakeholder & Organizational Dynamics) with analytical steps specific to corporate strategy. Four output formats (Investment Case, Board Narrative, Market Entry Strategy, Strategic Options Assessment) following consulting and corporate development conventions.

**When core is sufficient:** General competitive analysis, market entry evaluation without deep corporate strategy, product strategy decisions, or strategic recommendations that don't require consulting-style methodology.

---

## Software Engineering

**Domain:** Reliability engineering, security, technical leadership, and engineering-specific deliverables.

**Route here when:** The task involves SRE concerns (reliability, observability, incident response), security analysis (threat modeling, vulnerability assessment), engineering leadership decisions (technical strategy, team scaling), or engineering-convention deliverables (RFCs, ADRs, runbooks). Key signals: production system concerns, security-specific analysis, engineering org design, or deliverables that follow established engineering documentation patterns.

**What it adds beyond core:** Three specialized identities (SRE / Platform Engineer, Security Engineer, Staff+ Engineer / Tech Lead) with domain-specific reasoning styles and priorities. Four reasoning approaches (Code & Design Review, API Design, Performance & Scalability Analysis, Threat Modeling) with analytical steps specific to engineering disciplines. Four output formats (RFC, ADR, Runbook, Code Review Feedback) following standard engineering documentation conventions.

**When core is sufficient:** General system design, debugging, migration planning, or technical evaluation that the core Technical Architect identity and Technical reasoning family handle well. The core catalog covers most technical tasks — the engineering pack adds depth for tasks that require specific engineering discipline expertise or convention-following deliverables.

---

## Content & Communications

**Domain:** Content creation, editorial, copywriting, and content-specific deliverables.

**Route here when:** The task involves audience analysis beyond basic demographics, editorial judgment calls, content adaptation across channels, persuasion architecture, or content-convention deliverables (blog posts, content briefs, messaging frameworks, email sequences). Key signals: content strategy language (editorial calendar, content pillars, channel strategy), copywriting needs (conversion copy, brand voice), or deliverables that follow content marketing conventions.

**What it adds beyond core:** Three specialized identities (Writer / Editor, Content Strategist, Copywriter) that distinguish between strategic content thinking and execution-level writing. Four reasoning approaches (Audience Analysis, Editorial Judgment, Content Adaptation, Persuasion Architecture) with analytical steps specific to content creation. Four output formats (Blog Post / Article, Content Brief, Messaging Framework, Email Sequence) following content marketing conventions.

**When core is sufficient:** General messaging and positioning work, one-off communication tasks (emails, presentations), or narrative design that the core Communications Strategist identity handles well. The core catalog covers most communication tasks — the content pack adds depth for tasks requiring sustained content strategy or content-convention deliverables.

---

## Research & Analysis

**Domain:** Quantitative analysis, policy research, investigative inquiry, and research-specific deliverables.

**Route here when:** The task involves statistical or quantitative interpretation, systematic review methodology, causal analysis with methodological rigor, hypothesis-driven investigation, or research-convention deliverables (policy briefs, data analysis reports, literature reviews, briefing documents). Key signals: methodological language (sample size, statistical significance, causal inference), policy analysis needs, investigative framing, or deliverables that follow academic or policy research conventions.

**What it adds beyond core:** Three specialized identities (Data Analyst, Policy Analyst, Investigative Researcher) with domain-specific analytical orientations. Four reasoning approaches (Quantitative Interpretation, Systematic Review, Causal Analysis, Hypothesis-Driven Investigation) with analytical steps specific to rigorous research. Four output formats (Policy Brief, Data Analysis Report, Literature Review, Briefing Document) following research and policy conventions.

**When core is sufficient:** General evidence synthesis, landscape scans, or gap analysis that the core Research Synthesist identity and Research reasoning family handle well. The core catalog covers most analytical tasks — the research pack adds depth for tasks requiring formal research methodology or research-convention deliverables.

---

## Agentic & Context Engineering

**Domain:** AI agent system design, tool interface design, context architecture, and multi-turn agentic systems.

**Route here when:** The task involves designing agent system prompts, decomposing tasks into agent vs. workflow patterns, designing tool interfaces for AI agents, architecting context window management, planning failure modes and recovery for autonomous systems, or coordinating multi-agent systems. Key signals: agent design language (system prompts, tool definitions, context windows), autonomous system concerns (failure recovery, escalation), or deliverables specifically about AI system architecture.

**What it adds beyond core:** Three specialized identities (Agent System Designer, Agent Evaluator, Context Architect) focused on AI system design rather than general software architecture. Five reasoning approaches (Agent vs. Workflow Decomposition, Tool Interface Design, Context Window Architecture, Failure Mode & Recovery Design, Multi-Agent Coordination) with analytical steps specific to agentic system design. Four output formats (Agent System Prompt, Tool Definition Specification, Agent Architecture Blueprint, Context Management Plan) for AI system documentation.

**When core is sufficient:** General system design, technical evaluation, or architecture work that involves AI components but is not primarily about designing agent behavior or context management. The core Technical Architect identity handles most technical design — the agentic pack is specifically for tasks where the primary deliverable is the design of an AI agent system itself.

---

## Routing Decision Summary

| Task Signal | Route To |
|---|---|
| M&A, due diligence, board-level strategy, consulting deliverables | Business Strategy |
| SRE, security analysis, RFCs, ADRs, runbooks, engineering leadership | Software Engineering |
| Content strategy, editorial, copywriting, content briefs, email sequences | Content & Communications |
| Quantitative methods, policy analysis, systematic review, literature review | Research & Analysis |
| Agent design, tool interfaces, context windows, multi-agent coordination | Agentic & Context Engineering |
| Everything else | Core catalog (8 identities, 18 reasoning, 10 output) |

Domain packs are available as separate Skills (`rootnode-domain-business-strategy`, `rootnode-domain-software-engineering`, `rootnode-domain-content-communications`, `rootnode-domain-research-analysis`, `rootnode-domain-agentic-context`) if installed. When a domain pack is not installed, the core catalog still produces competent output — the domain pack adds specialized depth, not a fundamentally different capability.

---
name: notion-spec-to-implementation
description: Turns product or tech specs into concrete Notion tasks that Claude code can implement. Breaks down spec pages into detailed implementation plans with clear tasks, acceptance criteria, and progress tracking to guide development from requirements to completion.
---

# Spec to Implementation

Transforms specifications into actionable implementation plans with progress tracking. Fetches spec documents, extracts requirements, breaks down into tasks, and manages implementation workflow.

## Quick Start

When asked to implement a specification:

1. **Find spec**: Use Notion:notion-search to locate specification page
2. **Fetch spec**: Use Notion:notion-fetch to read specification content
3. **Extract requirements**: Parse and structure requirements from spec
4. **Create plan**: Use Notion:notion-create-pages for implementation plan
5. **Find task database**: Use Notion:notion-search to locate tasks database
6. **Create tasks**: Use Notion:notion-create-pages for individual tasks
7. **Update spec**: Link implementation plan back to specification

## Task Structure

Each task should include:
- Title (clear, actionable)
- Description (what needs to be done)
- Acceptance criteria (how to verify completion)
- Dependencies (what must be done first)
- Status (Not Started / In Progress / Complete / Blocked)
- Estimated effort (story points or hours)

## Implementation Plan Structure

The implementation plan should include:
- Phases with milestones
- Tasks organized by phase
- Dependencies between tasks
- Progress tracking (percentage complete)
- Links back to specification

## Bidirectional Linking

**Forward Links**: Update spec page with "Implementation" section linking to plan and tasks
**Backward Links**: Reference spec in plan and tasks with "Specification" section
**Bidirectional Traceability**: Maintain both directions for easy tracking

## Progress Tracking

**Plan Status**: Update with phase completion (Complete, In Progress %, Not Started) and overall percentage
**Task Aggregation**: Query task database by plan ID to generate summary (complete, in progress, blocked, not started)

## Change Management

**Detection**: Fetch updated spec, compare with plan, identify new requirements, assess impact
**Propagation**: Update plan, create new tasks, update affected tasks, add change note, notify via comments
**Change Log**: Track spec evolution with date, what changed, and impact

## Common Patterns

**Feature Flag**: Backend (behind flag) > Testing > Frontend (flagged) > Internal rollout > External rollout
**Database Migration**: Schema design > Migration script > Staging test > Production migration > Validation
**API Integration**: Contract definition > Mock implementation > Real implementation > Testing > Documentation

## Notes

This skill uses Notion MCP integration. The Notion workspace must be connected and accessible for the skill to function.

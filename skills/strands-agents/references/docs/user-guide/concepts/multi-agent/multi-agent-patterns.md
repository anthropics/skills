# Multi-agent Patterns

In Strands, building a system with multiple agents or complex tool chains can be approached in several ways. The three primary patterns you'll encounter are Graph, Swarm, and Workflow. While they all aim to solve complex problems, they have differences in their structures, execution workflows, and use cases.

To best help you decide which one is best for your problem, we will discuss them from core concepts, commonalities, and differences.

## Main Idea of Multi-agent System

Before we start comparing, Let's agree on a common concept. Multi-agent system is a system composed of multiple autonomous agents that interact with each other to achieve a mutual goal that is too complex or too large for any single agent to reach alone.

The key principles are:

- Orchestration: A controlling logic or structure to manage the flow of information and tasks between agents.
- Specialization: An agent has a specific role or expertise, and a set of tools that it can use.
- Collaboration: Agents communicate and share information to work upon each other's work.

Graph, Swarm, and Workflow are different methods of orchestration. Graph and Swarm are fundamental components in `strands-agents` and can also be used as tools from `strands-agents-tools`. We recommend using them from the SDK, while Workflow can only be used as a tool from `strands-agents-tools`. 

## High Level Commonality in Graph, Swarm and Workflow

They share some common things within Strands system:

- They all have the ultimate goal to solve complicated problems for users.
- They all use a single Strands `Agent` as the minimal unit of actions.
- They all involve passing information between different components to move toward a final answer.


## Difference in Graph, Swarm and Workflow

>⚠️ To be more explicit, the most difference you should consider among those patterns is **how the path of execution is determined**.

| Field                   | Graph                                                                                                                                 | Swarm                                                                                                                                                             | Workflow                                                                                                                          |
|-------------------------|---------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------|
| Core Concept            | A structured, developer-defined flowchart where an agent decides which path to take.                                                  | A dynamic, collaborative team of agents that autonomously hand off tasks.                                                                                         | A pre-defined Task Graph (DAG) executed as a single, non-conversational tool.                                                     |
| Structure               | A developer defines all nodes (agents) and edges (transitions) in advance.                                                            | A developer provides a pool of agents. The agents themselves decide the path.                                                                                     | A developer defines all tasks and their dependencies in code.                                                                     |
| Execution Flow          | Controlled but Dynamic. <br/>The flow follows graph edges, but an LLM's decision at each node determines the path.                    | Sequential & Autonomous.<br/> An agent performs a task and then uses a handoff_to_agent tool to pass control to the most suitable peer.                           | Deterministic & Parallel. <br/>The flow is fixed by the dependency graph. Independent tasks run in parallel.                      |
| Allow Cycle?            | Yes.                                                                                                                                  | Yes.                                                                                                                                                              | No.                                                                                                                               |
| State Sharing Mechanism | A single, shared dict object is passed to all agents, who can freely read and modify it.                                              | A "shared context" or working memory is available to all agents, containing the original request, task history, and knowledge from previous agents.               | The tool automatically captures task outputs and passes them as inputs to dependent tasks.                                        |
| Conversation History    | Full Transcript.<br/>The entire dialogue history is a key within the shared state, giving every agent complete and open context.      | Shared Transcript.<br/>The shared context provides a full history of agent handoffs and knowledge contributed by previous agents, available to the current agent. | Task-Specific context. <br/>A task receives a curated summary of relevant results from its dependencies, not the full history.    |
| Behavior Control        | The user's input at each step can directly influence which path the graph takes next.                                                 | The user's initial prompt defines the goal, but the swarm runs autonomously from there.                                                                           | The user's prompt can trigger a pre-defined workflow, but it cannot alter its internal structure.                                 |
| Scalability             | Scales well with process complexity (many branches, conditions).                                                                      | Scales with the number of specialized agents in the team and the complexity of the collaborative task.                                                            | Scales well for repeatable, complex operations.                                                                                   |
| Error handling          | Controllable.<br/> A developer can define explicit "error" edges to route the flow to a specific error-handling node if a step fails. | Agent-driven.<br/>An agent can decide to hand off to an error-handling specialist. The system relies on timeouts and handoff limits to prevent indefinite loops.  | Systemic. A failure in one task will halt all downstream dependent tasks. The entire workflow will likely enter a `Failed` state. |

## When to Use Each Pattern

Now you should have some general concept about the difference between patterns. Choosing the right pattern is critical for building an effective system.

### When to Use [Graph](./graph.md)

When you need a structured process that requires conditional logic, branching, or loops with deterministic execution flow. A `Graph` is perfect for modeling a business process or any task where the next step is decided by the outcome of the current one.

Some Examples:

- Interactive Customer Support: Routing a conversation based on user intent ("I have question about my order, I need to update my address, I need human assistance").
- Data Validation with Error Paths: An agent validates data and, based on the outcome, a conditional edge routes it to either a "processing" node or a pre-defined "error-handling" node.

### When to Use [Swarm](./swarm.md)

When your problem can be broken down into sub-tasks that benefit from different specialized perspectives. A `Swarm` is ideal for exploration, brainstorming, or synthesizing information from multiple sources through collaborative handoffs. It leverages agent specialization and shared context to generate diverse, comprehensive results.

Some Examples:

- Multidisciplinary Incident Response: A monitoring agent detects an issue and hands off to a network_specialist, who diagnoses it as a database problem and hands off to a database_admin.
- Software Development: As shown in the [`Swarm` documentation](./swarm.md#how-swarms-work), a researcher hands off to an architect, who hands off to a coder, who hands off to a reviewer. The path is emergent.

### When to Use [Workflow](./workflow.md)

When you have a complex but repeatable process that you want to encapsulate into a single, reliable, and reusable tool. A `Workflow` is a developer-defined task graph that an agent can execute as a single, powerful action.

Some Examples:

- Automated Data Pipelines: A fixed set of tasks to extract, analyze, and report on data, where independent analysis steps can run in parallel.
- Standard Business Processes: Onboarding a new employee by creating accounts, assigning training, and sending a welcome email, all triggered by a single agent action.

## Shared State Across Multi-Agent Patterns

Both Graph and Swarm patterns support passing shared state to all agents through the `invocation_state` parameter. This enables sharing context and configuration across agents without exposing it to the LLM.

### How Shared State Works

The `invocation_state` is automatically propagated to:

- All agents in the pattern via their `**kwargs`
- Tools via `ToolContext` when using `@tool(context=True)` - see [Python Tools](../tools/custom-tools.md#accessing-state-in-tools)
- Tool-related hooks (BeforeToolCallEvent, AfterToolCallEvent) - see [Hooks](../agents/hooks.md#accessing-invocation-state-in-hooks)

### Example Usage

```python
# Same invocation_state works for both patterns
shared_state = {
    "user_id": "user123",
    "session_id": "sess456",
    "debug_mode": True,
    "database_connection": db_connection_object
}

# Execute with Graph
result = graph(
    "Analyze customer data",
    invocation_state=shared_state
)

# Execute with Swarm (same shared_state)
result = swarm(
    "Analyze customer data", 
    invocation_state=shared_state
)
```

### Accessing Shared State in Tools

```python
from strands import tool, ToolContext

@tool(context=True)
def query_data(query: str, tool_context: ToolContext) -> str:
    user_id = tool_context.invocation_state.get("user_id")
    debug_mode = tool_context.invocation_state.get("debug_mode", False)
    # Use context for personalized queries...
```

### Important Distinctions

- **Shared State**: Configuration and objects passed via `invocation_state`, not visible in prompts
- **Pattern-Specific Data Flow**: Each pattern has its own mechanisms for passing data that the LLM should reason about including shared context for swarms and agent inputs for graphs

Use `invocation_state` for context and configuration that shouldn't appear in prompts, while using each pattern's specific data flow mechanisms for data the LLM should reason about.

## Conclusion

This guide has explored the three primary multi-agent patterns in Strands: Graph, Swarm, and Workflow. Each pattern serves distinct use cases based on how execution paths are determined and controlled. When choosing between patterns, consider your problem's complexity, the need for deterministic vs. emergent behavior, and whether you require cycles, parallel execution, or specific error handling approaches.

## Related Documentation

For detailed implementation guides and examples:

- [Graph Documentation](./graph.md)
- [Swarm Documentation](./swarm.md)
- [Workflow Documentation](./workflow.md)

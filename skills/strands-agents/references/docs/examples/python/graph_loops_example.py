#!/usr/bin/env python3
"""
# Graph with Loops Example

A demonstration of creating multi-agent graphs with feedback loops using Strands Agents.

## What This Example Shows

This example demonstrates:
- Creating graphs with conditional loops
- Custom deterministic nodes alongside AI agents
- Write-review-improve cycles
- Loop safety mechanisms
- State management across iterations

## Usage Examples

Basic usage:
```
python graph_loops_example.py
```

Import in your code:
```python
from examples.python.graph_loops_example import create_content_loop

# Create and run a content improvement loop
graph = create_content_loop()
result = graph("Write a haiku about programming")
print(result)
```

## Graph Structure

The example creates a feedback loop:
writer -> checker -> (loop back to writer OR proceed to finalizer)

The checker requires multiple iterations before approving content,
demonstrating how conditional loops work in practice.
"""

from strands import Agent
from strands.agent.agent_result import AgentResult
from strands.multiagent import GraphBuilder, MultiAgentBase, MultiAgentResult
from strands.multiagent.base import NodeResult, Status
from strands.types.content import ContentBlock, Message


class QualityChecker(MultiAgentBase):
    """Custom node that evaluates content quality."""
    
    def __init__(self, approval_after: int = 2):
        super().__init__()
        self.approval_after = approval_after
        self.iteration = 0
        self.name = "checker"
        
    async def invoke_async(self, task, invocation_state, **kwargs):
        self.iteration += 1
        approved = self.iteration >= self.approval_after
        
        msg = f"✅ Iteration {self.iteration}: APPROVED" if approved else f"⚠️ Iteration {self.iteration}: NEEDS REVISION"
        
        agent_result = AgentResult(
            stop_reason="end_turn",
            message=Message(role="assistant", content=[ContentBlock(text=msg)]),
            metrics=None,
            state={"approved": approved, "iteration": self.iteration}
        )
        
        return MultiAgentResult(
            status=Status.COMPLETED,
            results={self.name: NodeResult(result=agent_result, execution_time=10, status=Status.COMPLETED)},
            execution_count=1,
            execution_time=10
        )


def create_content_loop():
    """Create a graph with a write-review-improve feedback loop."""
    
    writer = Agent(
        name="writer",
        system_prompt="You are a content writer. Write or improve content based on the task. Keep responses concise."
    )
    
    finalizer = Agent(
        name="finalizer", 
        system_prompt="Polish the approved content into a professional format with a title."
    )
    
    checker = QualityChecker(approval_after=2)
    
    builder = GraphBuilder()
    builder.add_node(writer, "writer")
    builder.add_node(checker, "checker") 
    builder.add_node(finalizer, "finalizer")
    
    builder.add_edge("writer", "checker")
    
    def needs_revision(state):
        checker_result = state.results.get("checker")
        if not checker_result:
            return False
        multi_result = checker_result.result
        if hasattr(multi_result, 'results') and 'checker' in multi_result.results:
            agent_result = multi_result.results['checker'].result
            if hasattr(agent_result, 'state'):
                return not agent_result.state.get("approved", False)
        return True
    
    def is_approved(state):
        checker_result = state.results.get("checker")
        if not checker_result:
            return False
        multi_result = checker_result.result
        if hasattr(multi_result, 'results') and 'checker' in multi_result.results:
            agent_result = multi_result.results['checker'].result
            if hasattr(agent_result, 'state'):
                return agent_result.state.get("approved", False)
        return False
    
    builder.add_edge("checker", "writer", condition=needs_revision)
    builder.add_edge("checker", "finalizer", condition=is_approved)
    
    builder.set_entry_point("writer")
    builder.set_max_node_executions(10)
    builder.set_execution_timeout(60)
    builder.reset_on_revisit(True)
    
    return builder.build()


if __name__ == "__main__":
    print("\n🔄 Graph with Loops Example\n")
    print("This example demonstrates multi-agent graphs with feedback loops.")
    print("The graph will iterate through a write-review-improve cycle.")
    print("\nOptions:")
    print("  'demo' - Run demo with haiku task")
    print("  'exit' - Exit the program")
    print("\nOr enter any content creation task:")
    print("  'Write a short story about AI'")
    print("  'Create a product description for a smart watch'")

    while True:
        try:
            user_input = input("\n> ")

            if user_input.lower() == "exit":
                print("\nGoodbye! 👋")
                break
            elif user_input.lower() == "demo":
                user_input = "Write a haiku about programming loops"
                print(f"Running demo task: {user_input}")

            # Create and run the graph
            graph = create_content_loop()
            result = graph(user_input)
            
            # Show execution path
            print(f"\nExecution path: {' -> '.join([node.node_id for node in result.execution_order])}")
            
            # Show loop statistics
            node_visits = {}
            for node in result.execution_order:
                node_visits[node.node_id] = node_visits.get(node.node_id, 0) + 1
            
            loops = [f"{node_id} ({count}x)" for node_id, count in node_visits.items() if count > 1]
            if loops:
                print(f"Loops detected: {', '.join(loops)}")
            
            # Show final result
            if "finalizer" in result.results:
                print(f"\n✨ Final Result:\n{result.results['finalizer'].result}")

        except KeyboardInterrupt:
            print("\n\nExecution interrupted. Exiting...")
            break
        except Exception as e:
            print(f"\nAn error occurred: {str(e)}")
            print("Please try a different request.")
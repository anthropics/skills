# Agentic Workflow: Research Assistant - Multi-Agent Collaboration Example

This [example](https://github.com/strands-agents/docs/blob/main/docs/examples/python/agents_workflow.py) shows how to create a multi-agent workflow using Strands agents to perform web research, fact-checking, and report generation. It demonstrates specialized agent roles working together in sequence to process information.

## Overview

| Feature            | Description                            |
| ------------------ | -------------------------------------- |
| **Tools Used**     | http_request                           |
| **Agent Structure**| Multi-Agent Workflow (3 Agents)        |
| **Complexity**     | Intermediate                           |
| **Interaction**    | Command Line Interface                 |
| **Key Technique**  | Agent-to-Agent Communication           |

## Tools Overview

### http_request
The `http_request` tool enables the agent to make HTTP requests to retrieve information from the web. It supports GET, POST, PUT, and DELETE methods, handles URL encoding and response parsing, and returns structured data from web sources. While this tool is used in the example to gather information from the web, understanding its implementation details is not crucial to grasp the core concept of multi-agent workflows demonstrated in this example.

## Workflow Architecture

The Research Assistant example implements a three-agent workflow where each agent has a specific role and works with other agents to complete tasks that require multiple steps of processing:

1. **Researcher agent**: Gathers information from web sources using http_request tool
2. **Analyst agent**: Verifies facts and identifies key insights from research findings
3. **Writer agent**: Creates a final report based on the analysis

## Code Structure and Implementation

### 1. Agent Initialization

Each agent in the workflow is created with a system prompt that defines its role:

```python
# Researcher agent with web capabilities
researcher_agent = Agent(
    system_prompt=(
        "You are a Researcher Agent that gathers information from the web. "
        "1. Determine if the input is a research query or factual claim "
        "2. Use your research tools (http_request, retrieve) to find relevant information "
        "3. Include source URLs and keep findings under 500 words"
    ),
    callback_handler=None,
    tools=[http_request]
)

# Analyst agent for verification and insight extraction
analyst_agent = Agent(
    callback_handler=None,
    system_prompt=(
        "You are an Analyst Agent that verifies information. "
        "1. For factual claims: Rate accuracy from 1-5 and correct if needed "
        "2. For research queries: Identify 3-5 key insights "
        "3. Evaluate source reliability and keep analysis under 400 words"
    ),
)

# Writer agent for final report creation
writer_agent = Agent(
    system_prompt=(
        "You are a Writer Agent that creates clear reports. "
        "1. For fact-checks: State whether claims are true or false "
        "2. For research: Present key insights in a logical structure "
        "3. Keep reports under 500 words with brief source mentions"
    )
)
```

### 2. Workflow Orchestration

The workflow is orchestrated through a function that passes information between agents:

```python
def run_research_workflow(user_input):
    # Step 1: Researcher agent gathers web information
    researcher_response = researcher_agent(
        f"Research: '{user_input}'. Use your available tools to gather information from reliable sources.",
    )
    research_findings = str(researcher_response)
    
    # Step 2: Analyst agent verifies facts
    analyst_response = analyst_agent(
        f"Analyze these findings about '{user_input}':\n\n{research_findings}",
    )
    analysis = str(analyst_response)
    
    # Step 3: Writer agent creates report
    final_report = writer_agent(
        f"Create a report on '{user_input}' based on this analysis:\n\n{analysis}"
    )
    
    return final_report
```

### 3. Output Suppression

The example suppresses intermediate outputs during the initialization of the agents, showing users only the final result from the `Writer agent`:

```python
researcher_agent = Agent(
    system_prompt=(
        "You are a Researcher agent that gathers information from the web. "
        "1. Determine if the input is a research query or factual claim "
        "2. Use your research tools (http_request, retrieve) to find relevant information "
        "3. Include source URLs and keep findings under 500 words"
    ),
    callback_handler=None, # Suppresses output
    tools=[http_request]
)
```

Without this suppression, the default [callback_handler](https://github.com/strands-agents/sdk-python/blob/main/src/strands/handlers/callback_handler.py) would print all outputs to stdout, creating a cluttered experience with duplicate information from each agent's thinking process and tool calls. Suppressing the output creates a clean user experience by preventing intermediate outputs while still allowing responses to be captured programmatically and enabling proper information flow between agents. Instead of verbose agent outputs, the code provides concise progress feedback through simple print statements:

```python
print("\nProcessing: '{user_input}'")
print("\nStep 1: Researcher agent gathering web information...")
print("Research complete")
print("Passing research findings to Analyst agent...\n")
```

## Sample Queries and Responses

**Query 1**: What are quantum computers?

**Response**:

>RESEARCH REPORT: QUANTUM COMPUTERS
>
>Quantum computers are computing devices that use principles of quantum mechanics such as superposition and entanglement to perform calculations. Unlike classical 
>computers that use bits (0s and 1s), quantum computers use quantum bits or "qubits" that can exist in multiple states simultaneously.
>
>KEY INSIGHTS:
>1. Quantum computers excel at solving specific problems like factoring large numbers and simulating quantum systems that are impractical for classical computers.
>2. They use quantum properties including superposition (existing in multiple states simultaneously) and entanglement (particles becoming interconnected).
>3. Current quantum computers are still in early development, with limitations in qubit stability and error rates.
>
>APPLICATIONS:
>Quantum computers show promise for cryptography, drug discovery, materials science, optimization problems, and artificial intelligence.
>
>CHALLENGES:
>Quantum computers require extreme cooling, are prone to errors due to "decoherence," and developing practical, scaled-up versions remains technically challenging.
>
>Sources: IBM Quantum Computing, Nature Journal publications
>

**Query 2**: Lemon cures cancer

**Response**:

>FACT-CHECK REPORT: "LEMON CURES CANCER"
>
>CLAIM: Lemon cures cancer
>
>VERDICT: FALSE
>
>While lemons contain compounds with potential health benefits, the claim that "lemon cures cancer" is false and misleading.
>
>FACTS:
>1. Lemons contain vitamin C and plant compounds that may have antioxidant properties and health benefits.
>2. No scientific evidence supports lemons as a cure for any type of cancer.
>3. The American Cancer Society and other medical organizations do not recognize lemon as a cancer treatment.
>
>CONTEXT:
>Cancer is a group of diseases requiring professional medical treatment. While diet can play a role in health and cancer prevention, 
>no single food can cure cancer. Claims about "miracle cures" like lemon often spread through misinformation and can be dangerous when they lead people to delay or refuse proven medical treatments.
>
>RECOMMENDATION:
>Cancer patients should follow treatment plans prescribed by healthcare providers and discuss any complementary approaches with their medical team.
>
>Sources: American Cancer Society, National Cancer Institute, cancer research literature


**Query 3**: Tuesday comes before Monday in the week

**Response**:

>FACT-CHECK REPORT: "TUESDAY COMES BEFORE MONDAY IN THE WEEK"
>
>CLAIM: Tuesday comes before Monday in the week
>
>VERDICT: FALSE
>
>The claim that Tuesday comes before Monday in the week is incorrect according to the internationally accepted Gregorian calendar system.
>
>FACTS:
>1. In the standard Gregorian calendar, the seven-day week follows this order: Sunday, Monday, Tuesday, Wednesday, Thursday, Friday, Saturday.
>2. Monday is recognized as the first or second day of the week (depending on whether Sunday or Monday is considered the start of the week in a given culture).
>3. Tuesday always follows Monday in all standard calendar systems worldwide.
>
>The international standard ISO 8601 defines Monday as the first day of the week, with Tuesday as the second day, confirming that Tuesday does not come before Monday.
>
>HISTORICAL CONTEXT:
>The seven-day week structure has roots in ancient Babylonian, Jewish, and Roman calendar systems. While different cultures may consider different days as the start of 
>the week (Sunday in the US and Saturday in Jewish tradition), none place Tuesday before Monday in the sequence.
>
>Sources: International Organization for Standardization (ISO), Encyclopedia Britannica
>


## Extending the Example

Here are some ways to extend this agents workflow example:

1. **Add User Feedback Loop**: Allow users to ask for more detail after receiving the report
2. **Implement Parallel Research**: Modify the Researcher agent to gather information from multiple sources simultaneously
3. **Add Visual Content**: Enhance the Writer agent to include images or charts in the report
4. **Create a Web Interface**: Build a web UI for the workflow
5. **Add Memory**: Implement session memory so the system remembers previous research sessions


#!/usr/bin/env python3
"""
# Agentic Workflow: Research Assistant

This example demonstrates an agentic workflow using Strands agents with web research capabilities.

## Key Features
- Specialized agent roles working in sequence
- Direct passing of information between workflow stages
- Web research using http_request and retrieve tools
- Fact-checking and information synthesis

## How to Run
1. Navigate to the example directory
2. Run: python agents_workflow.py
3. Enter queries or claims at the prompt

## Example Queries
- "Thomas Edison invented the light bulb"
- "Tuesday comes before Monday in the week"

## Workflow Process
1. Researcher Agent: Gathers web information using multiple tools
2. Analyst Agent: Verifies facts and synthesizes findings
3. Writer Agent: Creates final report
"""

from strands import Agent
from strands_tools import http_request


def run_research_workflow(user_input):
    """
    Run a three-agent workflow for research and fact-checking with web sources.
    Shows progress logs during execution but presents only the final report to the user.
    
    Args:
        user_input: Research query or claim to verify
        
    Returns:
        str: The final report from the Writer Agent
    """
    
    print(f"\nProcessing: '{user_input}'")
    
    # Step 1: Researcher Agent with enhanced web capabilities
    print("\nStep 1: Researcher Agent gathering web information...")
    
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
    
    researcher_response = researcher_agent(
        f"Research: '{user_input}'. Use your available tools to gather information from reliable sources. "
        f"Focus on being concise and thorough, but limit web requests to 1-2 sources.",
    )
    
    # Extract only the relevant content from the researcher response
    research_findings = str(researcher_response)
    
    print("Research complete")
    print("Passing research findings to Analyst Agent...\n")
    
    # Step 2: Analyst Agent to verify facts
    print("Step 2: Analyst Agent analyzing findings...")
    
    analyst_agent = Agent(
        system_prompt=(
            "You are an Analyst Agent that verifies information. "
            "1. For factual claims: Rate accuracy from 1-5 and correct if needed "
            "2. For research queries: Identify 3-5 key insights "
            "3. Evaluate source reliability and keep analysis under 400 words"
        ),
        callback_handler=None
    )

    analyst_response = analyst_agent(
        f"Analyze these findings about '{user_input}':\n\n{research_findings}",
    )
    
    # Extract only the relevant content from the analyst response
    analysis = str(analyst_response)
    
    print("Analysis complete")
    print("Passing analysis to Writer Agent...\n")
    
    # Step 3: Writer Agent to create report
    print("Step 3: Writer Agent creating final report...")
    
    writer_agent = Agent(
        system_prompt=(
            "You are a Writer Agent that creates clear reports. "
            "1. For fact-checks: State whether claims are true or false "
            "2. For research: Present key insights in a logical structure "
            "3. Keep reports under 500 words with brief source mentions"
        )
    )
    
    # Execute the Writer Agent with the analysis (output is shown to user)
    final_report = writer_agent(
        f"Create a report on '{user_input}' based on this analysis:\n\n{analysis}"
    )
    
    print("Report creation complete")
    
    # Return the final report
    return final_report


if __name__ == "__main__":
    # Print welcome message
    print("\nAgentic Workflow: Research Assistant\n")
    print("This demo shows Strands agents in a workflow with web research.")
    print("Try research questions or fact-check claims.")
    print("\nExamples:")
    print("- \"What are quantum computers?\"")
    print("- \"Lemon cures cancer\"")
    print("- \"Tuesday comes before Monday in the week\"")
    
    # Interactive loop
    while True:
        try:
            user_input = input("\n> ")
            if user_input.lower() == "exit":
                print("\nGoodbye!")
                break
            
            # Process the input through the workflow of agents
            final_report = run_research_workflow(user_input)
        except KeyboardInterrupt:
            print("\n\nExecution interrupted. Exiting...")
            break
        except Exception as e:
            print(f"\nAn error occurred: {str(e)}")
            print("Please try a different request.")

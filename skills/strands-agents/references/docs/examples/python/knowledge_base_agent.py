#!/usr/bin/env python3
"""
# Knowledge Base Agent

This example demonstrates a Strands agent that can intelligently determine 
whether to store information to a knowledge base or retrieve information from it
based on the user's query.

## Key Features
- Clear determination of store vs. retrieve actions
- Simple, user-friendly interactions
- Clean, readable output

## How to Run
1. Navigate to the example directory
2. Run: python knowledge_base_agent.py
3. Enter queries or information at the prompt

## Example Queries
- "Remember that my birthday is on July 25"
- "What day is my birthday?"
- "The capital of France is Paris"
"""

import os
import sys
from pathlib import Path
from strands import Agent
from strands_tools import use_llm, memory

# Set knowledge base ID (can be overridden by environment variable)
DEFAULT_KB_ID = "demokb123"
KB_ID = os.environ.get("STRANDS_KNOWLEDGE_BASE_ID")

if not KB_ID:
    print("\n⚠️  Warning: STRANDS_KNOWLEDGE_BASE_ID environment variable is not set!")
    print("To use a real knowledge base, please set the STRANDS_KNOWLEDGE_BASE_ID environment variable.")
    print("For example: export STRANDS_KNOWLEDGE_BASE_ID=your_kb_id")
    print(f"Using DEFAULT_KB_ID '{DEFAULT_KB_ID}' for demonstration purposes only.")
    KB_ID = DEFAULT_KB_ID
else:
    print(f"Using Knowledge Base ID: {KB_ID}")

# System prompt to determine action
ACTION_SYSTEM_PROMPT = """
You are a knowledge base assistant focusing ONLY on classifying user queries.
Your task is to determine whether a user query requires STORING information to a knowledge base
or RETRIEVING information from a knowledge base.

Reply with EXACTLY ONE WORD - either "store" or "retrieve".
DO NOT include any explanations or other text.

Examples:
- "Remember that my birthday is July 4" -> "store"
- "What's my birthday?" -> "retrieve"
- "The capital of France is Paris" -> "store"
- "What is the capital of France?" -> "retrieve"
- "My name is John" -> "store" 
- "Who am I?" -> "retrieve"
- "I live in Seattle" -> "store"
- "Where do I live?" -> "retrieve"

Only respond with "store" or "retrieve" - no explanation, prefix, or any other text.
"""

# System prompt for generating answers from retrieved information
ANSWER_SYSTEM_PROMPT = """
You are a helpful knowledge assistant that provides clear, concise answers 
based on information retrieved from a knowledge base.

The information from the knowledge base contains document IDs, titles, 
content previews and relevance scores. Focus on the actual content and 
ignore the metadata.

Your responses should:
1. Be direct and to the point
2. Not mention the source of information (like document IDs or scores)
3. Not include any metadata or technical details
4. Be conversational but brief
5. Acknowledge when information is conflicting or missing
6. Begin the response with \n

When analyzing the knowledge base results:
- Higher scores (closer to 1.0) indicate more relevant results
- Look for patterns across multiple results
- Prioritize information from results with higher scores
- Ignore any JSON formatting or technical elements in the content

Example response for conflicting information:
"Based on my records, I have both July 4 and August 8 listed as your birthday. Could you clarify which date is correct?"

Example response for clear information:
"Your birthday is on July 4."

Example response for missing information:
"I don't have any information about your birthday stored."
"""

def determine_action(agent, query):
    """Determine if the query is a store or retrieve action."""
    result = agent.tool.use_llm(
        prompt=f"Query: {query}",
        system_prompt=ACTION_SYSTEM_PROMPT
    )
    
    # Clean and extract the action
    action_text = str(result).lower().strip()
    
    # Default to retrieve if response isn't clear
    if "store" in action_text:
        return "store"
    else:
        return "retrieve"

def run_kb_agent(query):
    """Process a user query with the knowledge base agent."""
    agent = Agent(tools=[memory, use_llm])
    
    # Determine the action - store or retrieve
    action = determine_action(agent, query)
    
    if action == "store":
        # For store actions, store the full query
        agent.tool.memory(action="store", content=query)
        print("\nI've stored this information.")
    else:
        # For retrieve actions, query the knowledge base with appropriate parameters
        result = agent.tool.memory(
            action="retrieve", 
            query=query,
            min_score=0.4,  # Set reasonable minimum score threshold
            max_results=9   # Retrieve a good number of results
        )
        # Convert the result to a string to extract just the content text
        result_str = str(result)
        
        # Generate a clear, conversational answer using the retrieved information
        answer = agent.tool.use_llm(
            prompt=f"User question: \"{query}\"\n\nInformation from knowledge base:\n{result_str}\n\nStart your answer with newline character and provide a helpful answer based on this information:",
            system_prompt=ANSWER_SYSTEM_PROMPT
        )

if __name__ == "__main__":
    # Print welcome message
    print("\n🧠 Knowledge Base Agent 🧠\n")
    print("This agent helps you store and retrieve information from your knowledge base.")
    print("Try commands like:")
    print("- \"Remember that my birthday is on July 25\"")
    print("- \"What day is my birthday?\"")
    print("\nType your request below or 'exit' to quit:")
    
    # Interactive loop
    while True:
        try:
            user_input = input("\n> ")
            if user_input.lower() in ["exit", "quit"]:
                print("\nGoodbye! 👋")
                break
            
            if not user_input.strip():
                continue
                
            # Process the input through the knowledge base agent
            print("Processing...")
            run_kb_agent(user_input)
            
        except KeyboardInterrupt:
            print("\n\nExecution interrupted. Exiting...")
            break
        except Exception as e:
            print(f"\nAn error occurred: {str(e)}")

from strands import Agent, tool
import json

GENERAL_ASSISTANT_SYSTEM_PROMPT = """
You are GeneralAssist, a concise general knowledge assistant for topics outside specialized domains. Your key characteristics are:

1. Response Style:
   - Always begin by acknowledging that you are not an expert in this specific area
   - Use phrases like "While I'm not an expert in this area..." or "I don't have specialized expertise, but..."
   - Provide brief, direct answers after this disclaimer
   - Focus on facts and clarity
   - Avoid unnecessary elaboration
   - Use simple, accessible language

2. Knowledge Areas:
   - General knowledge topics
   - Basic information requests
   - Simple explanations of concepts
   - Non-specialized queries

3. Interaction Approach:
   - Always include the non-expert disclaimer in every response
   - Answer with brevity (2-3 sentences when possible)
   - Use bullet points for multiple items
   - State clearly if information is limited
   - Suggest specialized assistance when appropriate

Always maintain accuracy while prioritizing conciseness and clarity in every response, and never forget to acknowledge your non-expert status at the beginning of your responses.
"""


@tool
def general_assistant(query: str) -> str:
    """
    Handle general knowledge queries that fall outside specialized domains.
    Provides concise, accurate responses to non-specialized questions.
    
    Args:
        query: The user's general knowledge question
        
    Returns:
        A concise response to the general knowledge query
    """
    # Format the query for the agent
    formatted_query = f"Answer this general knowledge question concisely, remembering to start by acknowledging that you are not an expert in this specific area: {query}"
    
    try:
        print("Routed to General Assistant")
        general_agent = Agent(
            system_prompt=GENERAL_ASSISTANT_SYSTEM_PROMPT,
            tools=[],  # No specialized tools needed for general knowledge
        )
        agent_response = general_agent(formatted_query)
        text_response = str(agent_response)

        if len(text_response) > 0:
            return text_response
        
        return "Sorry, I couldn't provide an answer to your question."
    except Exception as e:
        # Return error message
        return f"Error processing your question: {str(e)}"
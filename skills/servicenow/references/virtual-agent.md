# Virtual Agent

## Overview

Virtual Agent is ServiceNow's AI-powered chatbot that handles employee and customer self-service through conversational interfaces. It integrates with NLU (Natural Language Understanding), the Service Catalog, Knowledge Base, and custom server-side scripts.

### Channels
```
Supported channels:
  - ServiceNow Service Portal (web chat widget)
  - Microsoft Teams
  - Slack
  - Web API (custom integrations)
  - Mobile (Now Mobile app)
  - Employee Center
  - Customer Service Portal (CSM)
```

## NLU (Natural Language Understanding)

### NLU Models
```
Navigate: Virtual Agent > NLU Models

Model types:
  - Intent-based: maps user utterances to intents
  - ServiceNow NLU: built-in model (no external dependency)
  - IBM Watson: external NLU engine
  - Google Dialogflow: external NLU engine
  - Microsoft LUIS: external NLU engine

Recommendation: Use ServiceNow NLU (simplest, no extra licensing)
```

### Creating Intents
```
Navigate: Virtual Agent > NLU > Intents

Intent structure:
  - Name: descriptive (e.g., "Reset Password")
  - Model: which NLU model
  - Utterances: example phrases (minimum 15-20 for accuracy)
  
Example — Password Reset Intent:
  Utterances:
    - "I forgot my password"
    - "Reset my password"
    - "Can't log in to my account"
    - "Password expired"
    - "I need to change my password"
    - "Locked out of my account"
    - "Help me reset my credentials"
    - "My password isn't working"
    - "How do I reset my password"
    - "I'm having trouble signing in"
    - "Account locked"
    - "Password doesn't work anymore"
    - "Need a new password"
    - "Can you help me with my login"
    - "Unable to access my account"
    
Tips:
  - Vary sentence structure and vocabulary
  - Include misspellings users commonly make
  - Add both formal and informal phrasing
  - 15-20 utterances minimum per intent
  - Avoid overlapping utterances between intents
```

### Entities
```
Navigate: Virtual Agent > NLU > Entities

Entity types:
  - System entities: date, time, number, email (built-in)
  - Custom entities: application-specific values
  
Example — Department Entity:
  Name: department
  Values:
    - IT (synonyms: information technology, tech support)
    - HR (synonyms: human resources, people team)
    - Finance (synonyms: accounting, billing)
    - Facilities (synonyms: building, office)
    
Usage in utterances:
  "I need help from {department}"
  "Connect me to {department}"
```

### Training & Testing
```
Navigate: Virtual Agent > NLU > Model Testing

Training:
  1. Add utterances to intents
  2. Click "Train" on the model
  3. Wait for training to complete (1-5 minutes)
  
Testing:
  - Test Utterances tab: type phrases, see predicted intent
  - Confusion matrix: see where intents overlap
  - Batch testing: upload CSV of test phrases
  
Accuracy targets:
  - >90% intent classification accuracy
  - <5% confusion between intents
  - Test with 50+ phrases per intent for production
```

## Topics (Conversation Flows)

### Topic Structure
```
Navigate: Virtual Agent > Designer

Topic = a conversation flow that handles one user intent

Structure:
  Topic: Password Reset
  ├── Greeting node
  │   └── "I can help you reset your password."
  ├── User Input node (collect info)
  │   └── "Which account needs a reset?"
  │       ├── Choice: Network/AD account
  │       └── Choice: Application-specific account
  ├── Script node (server-side logic)
  │   └── Look up user, validate identity
  ├── Bot Response node
  │   └── "I've sent a reset link to your email."
  └── End node
      └── "Is there anything else I can help with?"
```

### Topic Node Types

#### Greeting / Bot Response
```
Text output nodes:
  - Static text: fixed message
  - Dynamic text: include variables ${variable_name}
  - Rich content: links, images, cards
  - Carousel: multiple cards user can swipe
  
Example:
  "Hi ${user.first_name}! I can see you're in the ${user.department} department. 
   How can I help you today?"
```

#### User Input
```
Input types:
  - Text: free-form text entry
  - Choice: buttons/quick replies (up to 10 options)
  - Date/Time picker
  - File upload
  - Lookup: reference field search
  - Number
  - Email
  
Choice example:
  Prompt: "What type of request?"
  Choices:
    - "New Software" → routes to software topic
    - "Hardware Issue" → routes to hardware topic  
    - "Access Request" → routes to access topic
    - "Other" → routes to general inquiry
```

#### Script Node (Server-Side)
```javascript
// Script node — execute server-side logic
(function execute() {
    // Access topic variables
    var userId = vaSystem.getUser();
    var inputText = vaInputs.get('user_response');
    
    // GlideRecord queries
    var gr = new GlideRecord('sys_user');
    if (gr.get(userId)) {
        vaVars.user_name = gr.getValue('name');
        vaVars.user_email = gr.getValue('email');
        vaVars.user_department = gr.department.getDisplayValue();
        vaVars.user_manager = gr.manager.getDisplayValue();
    }
    
    // Check for open incidents
    var inc = new GlideRecord('incident');
    inc.addQuery('caller_id', userId);
    inc.addActiveQuery();
    inc.addQuery('short_description', 'CONTAINS', inputText);
    inc.setLimit(3);
    inc.query();
    
    var openIncidents = [];
    while (inc.next()) {
        openIncidents.push({
            number: inc.getValue('number'),
            description: inc.getValue('short_description'),
            state: inc.state.getDisplayValue()
        });
    }
    
    vaVars.has_existing = openIncidents.length > 0;
    vaVars.existing_incidents = JSON.stringify(openIncidents);
})();
```

#### Decision Node (Branching)
```
Branch based on:
  - Topic variable values
  - Script output
  - User role/group membership
  - NLU entity values
  
Example:
  Condition: vaVars.has_existing == true
    → Yes: "I found existing incidents. Would you like to check status?"
    → No: "Let me create a new incident for you."
```

#### Flow Trigger Node
```
Execute a Flow Designer flow from within a topic:
  - Pass topic variables as flow inputs
  - Receive flow outputs back into topic
  - Wait for flow completion or run async
  
Use cases:
  - Create catalog request
  - Run approval workflow
  - Execute automated remediation
  - Look up complex data
```

#### Create Record Node
```
Create records directly from the topic:
  - Table: incident, sc_req_item, hr_case, etc.
  - Field mapping: topic variables → record fields
  - Return: sys_id, number for confirmation
  
Example — Create Incident:
  Table: incident
  Mappings:
    short_description = ${user_issue_summary}
    description = ${user_detailed_description}
    caller_id = ${sys_user}
    category = ${selected_category}
    urgency = ${selected_urgency}
  Output variable: created_incident_number
```

#### Knowledge Search Node
```
Search knowledge base within conversation:
  - Search term: from user input variable
  - Knowledge base: specific or all
  - Display: article cards with links
  - Deflection: if article solves issue, close topic
  
Configuration:
  Search query: ${user_issue_description}
  Max results: 3
  If user selects article → End topic (deflected)
  If user says "not helpful" → Continue to create incident
```

### Topic Variables
```
Variable types:
  - String, Integer, Boolean
  - Reference (to any table)
  - Date/Time
  - JSON (complex objects)
  
System variables (auto-available):
  - vaSystem.getUser() → current user sys_id
  - vaSystem.getChannel() → chat channel name
  - vaSystem.getLanguage() → user's language
  - vaSystem.getTimezone() → user's timezone
  
Setting/Getting variables in scripts:
  vaVars.my_variable = 'value';          // Set
  var val = vaVars.my_variable;          // Get
  vaInputs.get('input_name');           // Get user input
  vaOutputs.set('output_name', value);  // Set output for next node
```

## Now Assist (GenAI) Integration

### Virtual Agent + Now Assist
```
Zurich+ features:
  - Generative AI fallback: if no intent matches, 
    Now Assist generates a response from knowledge base
  - Summarization: VA can summarize long KB articles
  - Suggested intents: Now Assist suggests new intents 
    based on unmatched conversations
  - Conversation analytics: AI-powered topic gap analysis
  
Configuration:
  Navigate: Now Assist > Virtual Agent Settings
  Enable: "Generative AI topic"
  Knowledge sources: select knowledge bases for grounding
```

### AI Search in Topics
```
Node type: AI Search
  - Searches across Knowledge, Service Catalog, Communities
  - Returns AI-summarized answers
  - Includes source links for verification
  - Fallback if VA can't match intent
```

## Multi-Language Support

```
Navigate: Virtual Agent > Localization

Setup:
  1. Enable languages in system settings
  2. Create translated versions of topics
  3. Map intents to language-specific NLU models
  4. Translate bot responses, choices, prompts
  
Automatic detection:
  - User's language preference (sys_user.preferred_language)
  - Browser language header
  - Manual language selection in chat widget

Translation approach:
  - Separate NLU model per language (best accuracy)
  - OR single model with multi-language utterances (simpler)
```

## Analytics & Improvement

### Key Metrics
```
Navigate: Virtual Agent > Analytics Dashboard

Metrics:
  - Containment rate: % resolved without human agent
  - Deflection rate: % handled by KB article
  - Abandonment rate: % who leave mid-conversation
  - Average conversation length (turns)
  - Intent match rate: % of utterances matched
  - Escalation rate: % transferred to live agent
  - CSAT: post-conversation satisfaction score
  
Targets:
  - Containment: >60% for common topics
  - Intent match: >85%
  - Abandonment: <15%
```

### Conversation Analysis
```
Navigate: Virtual Agent > Conversations

Review:
  - Full conversation transcripts
  - Unmatched utterances (intent gaps)
  - Conversation paths (where users get stuck)
  - Feedback analysis (thumbs up/down per topic)
  
Improvement workflow:
  1. Review unmatched utterances weekly
  2. Create new intents or add utterances to existing
  3. Retrain NLU model
  4. Analyze abandonment points in topics
  5. Simplify or add branches where users get stuck
```

## Live Agent Handoff

### Escalation to Human Agent
```
Topic node: Transfer to Agent

Configuration:
  - Queue: which assignment group receives the chat
  - Context passing: include conversation history
  - Wait message: "Connecting you to a live agent..."
  - Estimated wait time display
  - Fallback: if no agents available → create incident instead
  
Script for custom escalation:
```
```javascript
// Pre-escalation script — gather context
(function execute() {
    // Package conversation context for the agent
    var context = {
        user_issue: vaVars.issue_summary,
        attempted_solutions: vaVars.solutions_tried,
        category: vaVars.category,
        priority: vaVars.detected_priority,
        conversation_turns: vaVars.turn_count
    };
    
    // Set agent-visible context
    vaVars.escalation_context = JSON.stringify(context);
    
    // Create interaction record for tracking
    var interaction = new GlideRecord('interaction');
    interaction.initialize();
    interaction.setValue('type', 'chat');
    interaction.setValue('opened_for', vaSystem.getUser());
    interaction.setValue('short_description', vaVars.issue_summary);
    interaction.insert();
    
    vaVars.interaction_id = interaction.getUniqueValue();
})();
```

### Agent Workspace Chat
```
When escalated, agent sees:
  - Full conversation transcript
  - User details (name, department, location)
  - Context variables from VA topic
  - Suggested knowledge articles
  - Quick actions (create incident, check status)
  
Configuration:
  Navigate: Workspace Experience > Agent Chat
  - Queue management
  - Capacity rules (max concurrent chats per agent)
  - Auto-accept settings
  - Canned responses
```

## Virtual Agent Designer Tips

### Topic Design Patterns
```
1. Greeting → Identify Intent → Collect Info → Action → Confirm → End
2. Keep topics focused — one intent per topic
3. Max 7 conversation turns before resolution or escalation
4. Always offer escalation to human agent
5. Use quick replies over free text when possible
6. Confirm before taking action ("I'll create an incident. Proceed?")
7. Handle "I don't know" and "none of these" gracefully
8. End every topic with "Anything else I can help with?"
```

### Common Pitfalls
```
- Too many choices (>5 buttons) — users won't read them all
- Deep conversation trees — users abandon after 4-5 nodes
- No fallback for unmatched intents — user gets stuck
- Assuming user knows ServiceNow terms — use plain language
- Not testing on mobile — chat widget renders differently
- Ignoring analytics — launch and forget = declining usage
- Single-language only — limits adoption in global orgs
```

## Best Practices

1. **Start with top 10 IT requests** — password reset, software install, hardware request
2. **15+ utterances per intent** — less = poor recognition
3. **Test with real users** before production — their language differs from yours
4. **Measure containment** — if VA can't resolve, it's just an extra step before human
5. **Review unmatched weekly** — biggest source of improvement
6. **Quick replies > free text** — guided paths = higher completion
7. **Always offer human option** — users get frustrated when trapped in bot loops
8. **KB integration** — deflection through existing knowledge is highest ROI
9. **Channel-specific testing** — Teams/Slack render differently than portal
10. **Iterate monthly** — VA is never "done," always improving

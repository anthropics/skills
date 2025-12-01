# Testing Guide for DealMachine AI Agent

This guide provides test scenarios for each of the 10 skills to ensure they're working correctly.

## Prerequisites

Before testing:
1. ✅ DealMachine API key configured in `.env`
2. ✅ Skills installed in Claude or ChatGPT
3. ✅ Test lead data available in your DealMachine account

---

## Test Scenario 1: Lead List Retriever

### Test Commands

```
Test 1.1: Basic Retrieval
"Show me my DealMachine leads"

Expected: List of leads with addresses, owners, status

Test 1.2: Filtered Search
"Show me vacant properties with high equity"

Expected: Filtered list matching criteria

Test 1.3: Pagination
"Show me leads 50-100"

Expected: Next page of results
```

### Success Criteria
- ✅ Returns leads from DealMachine API
- ✅ Displays key information clearly
- ✅ Filtering works correctly
- ✅ Handles empty results gracefully

---

## Test Scenario 2: Lead Ranker

### Test Commands

```
Test 2.1: Rank All Leads
"Rank my leads by likelihood to sell"

Expected: Scored list (0-100) with hot/warm/qualified/cold tiers

Test 2.2: Rank Specific Subset
"Rank my 25 vacant properties"

Expected: Ranked list of just vacant properties

Test 2.3: Custom Scoring
"Rank leads but prioritize vacancy over equity"

Expected: Adjusted scores with new weighting
```

### Success Criteria
- ✅ Calculates scores based on multiple factors
- ✅ Shows score breakdown for each lead
- ✅ Groups into tiers correctly
- ✅ Provides reasoning for scores
- ✅ Offers campaign recommendations

---

## Test Scenario 3: Lead Analyzer

### Test Commands

```
Test 3.1: Full Analysis
"Analyze lead 789 Pine Road in detail"

Expected: Comprehensive analysis report

Test 3.2: Quick Analysis
"Give me a quick analysis of 123 Oak Street"

Expected: Condensed summary

Test 3.3: Deal Structure Comparison
"Show me flip vs rental vs wholesale options for 789 Pine Road"

Expected: Comparison table with ROI for each strategy
```

### Success Criteria
- ✅ Pulls all available lead data
- ✅ Provides property and owner analysis
- ✅ Calculates deal structures
- ✅ Offers negotiation strategies
- ✅ Identifies risks and opportunities

---

## Test Scenario 4: Campaign Budget Planner

### Test Commands

```
Test 4.1: Budget Planning
"I have $500 for marketing, help me create a budget"

Expected: Detailed budget breakdown by campaign tier

Test 4.2: Lead Allocation
"How should I allocate budget across my 100 leads?"

Expected: Strategy based on lead tiers and scores

Test 4.3: ROI Projection
"What's my expected ROI with $1000 budget?"

Expected: Conservative and optimistic projections
```

### Success Criteria
- ✅ Creates realistic budget allocations
- ✅ Calculates costs correctly ($0.57/mail)
- ✅ Projects response rates
- ✅ Estimates deals and ROI
- ✅ Provides timeline projections

---

## Test Scenario 5: Mail Campaign Creator

### Test Commands

```
Test 5.1: Create Campaign
"Create a campaign for my 15 tax delinquent leads"

Expected: Campaign with sequence, messaging, timeline

Test 5.2: Multi-Campaign Strategy
"Create campaigns for hot, warm, and qualified leads"

Expected: 3 different campaigns with appropriate messaging

Test 5.3: Custom Sequence
"I need a 3-step campaign for senior owners"

Expected: Senior-friendly messaging, gentle approach
```

### Success Criteria
- ✅ Recommends appropriate sequence length
- ✅ Customizes messaging by lead type
- ✅ Calculates costs correctly
- ✅ Sets appropriate timing
- ✅ Provides campaign templates

---

## Test Scenario 6: Lead Tag Manager

### Test Commands

```
Test 6.1: Tag Addition
"Tag all vacant leads with 'Vacant Property'"

Expected: Bulk tagging operation

Test 6.2: Smart Tagging
"Set up auto-tagging rules for hot leads"

Expected: Rule-based tagging system

Test 6.3: Tag Organization
"Show me all leads tagged 'Hot Lead' and 'Tax Delinquent'"

Expected: Filtered list by multiple tags
```

### Success Criteria
- ✅ Creates and applies tags via API
- ✅ Handles bulk operations
- ✅ Provides tag analytics
- ✅ Suggests tag organization
- ✅ Updates tags as lead status changes

---

## Test Scenario 7: Lead Note Creator

### Test Commands

```
Test 7.1: Contact Note
"I just called 789 Pine Road, owner is interested. Create a note."

Expected: Structured contact note with follow-up

Test 7.2: Template Note
"Create a property inspection note for 123 Oak St"

Expected: Template-based inspection note

Test 7.3: Note Search
"Find all notes mentioning 'tax delinquent'"

Expected: Search results across all notes
```

### Success Criteria
- ✅ Creates notes via API
- ✅ Provides templates for common note types
- ✅ Structures notes consistently
- ✅ Tracks follow-up actions
- ✅ Allows note search and retrieval

---

## Test Scenario 8: Campaign Monitor

### Test Commands

```
Test 8.1: Campaign Status
"How's my tax relief campaign performing?"

Expected: Detailed performance dashboard

Test 8.2: Multi-Campaign Comparison
"Compare all my active campaigns"

Expected: Comparison table with metrics

Test 8.3: Response Tracking
"Show me all responses this week"

Expected: List of responses with quality ratings
```

### Success Criteria
- ✅ Tracks delivery status
- ✅ Calculates response rates
- ✅ Monitors budget spend
- ✅ Provides alerts for responses
- ✅ Offers optimization recommendations

---

## Test Scenario 9: ROI Calculator

### Test Commands

```
Test 9.1: Fix & Flip ROI
"Calculate fix & flip ROI for 789 Pine Road at $240k"

Expected: Detailed ROI calculation with all costs

Test 9.2: Rental Analysis
"Should I flip or rent this property?"

Expected: Comparison of both strategies

Test 9.3: Marketing ROI
"What's my marketing ROI for Q1?"

Expected: Campaign-level ROI analysis
```

### Success Criteria
- ✅ Accurate calculations for all deal types
- ✅ Includes all costs (hidden costs too)
- ✅ Provides sensitivity analysis
- ✅ Compares multiple strategies
- ✅ Shows annualized ROI

---

## Test Scenario 10: Investment Plan Wizard

### Test Commands

```
Test 10.1: Create New Plan
"Help me create an investment plan"

Expected: Interactive wizard with questions

Test 10.2: Beginner Plan
[Answer questions as beginner with $10k budget]

Expected: Wholesaling-focused plan with 90-day roadmap

Test 10.3: Quarterly Review
"Review my plan progress"

Expected: Actual vs projected analysis with recommendations
```

### Success Criteria
- ✅ Interactive questioning flow
- ✅ Customizes plan to user profile
- ✅ Creates actionable timelines
- ✅ Sets realistic goals
- ✅ Provides ongoing guidance

---

## Integration Test

### End-to-End Workflow

```
Test I.1: Complete Lead-to-Deal Flow

Step 1: "Show me my DealMachine leads"
Step 2: "Rank these leads"
Step 3: "Analyze the top lead in detail"
Step 4: "Calculate ROI if I wholesale this at $240k purchase"
Step 5: "Create a note documenting this analysis"
Step 6: "Tag this lead as 'Hot - Ready for Offer'"

Expected: Seamless workflow across all skills
```

### Success Criteria
- ✅ Skills work together seamlessly
- ✅ Data flows between skills
- ✅ Context is maintained
- ✅ Recommendations are consistent

---

## Performance Testing

### API Rate Limits

```
Test P.1: High Volume
"Rank 200 leads"

Expected: Handles without hitting rate limits (10 req/sec)

Test P.2: Bulk Operations
"Tag 100 leads with 'Q1 Campaign'"

Expected: Batches requests appropriately
```

### Success Criteria
- ✅ Respects rate limits
- ✅ Handles large data sets
- ✅ Provides progress indicators
- ✅ Recovers from errors gracefully

---

## Error Handling Tests

### Test Error Scenarios

```
Test E.1: Invalid API Key
[Set invalid DEALMACHINE_API_KEY]
"Show me my leads"

Expected: Clear error message about API key

Test E.2: Network Error
[Simulate network failure]
"Rank my leads"

Expected: Retry logic with user notification

Test E.3: Missing Data
"Analyze lead with ID 'nonexistent'"

Expected: Graceful handling with helpful message
```

### Success Criteria
- ✅ Clear error messages
- ✅ Suggests solutions
- ✅ Doesn't crash
- ✅ Maintains conversation context

---

## Validation Checklist

After testing all scenarios, verify:

- [ ] All 10 skills respond to commands
- [ ] API integration works correctly
- [ ] Calculations are accurate
- [ ] Data flows between skills
- [ ] Error handling is robust
- [ ] Performance is acceptable
- [ ] Documentation matches behavior
- [ ] User experience is smooth

---

## Reporting Issues

If you find issues during testing:

1. Note the exact command used
2. Record the expected vs actual behavior
3. Include any error messages
4. Note your environment (Claude/ChatGPT, version)
5. Open an issue on GitHub with these details

---

## Test Data Setup

For comprehensive testing, ensure your DealMachine account has:

- At least 30 leads
- Mix of property types (SFR, multi-family)
- Various owner types (individual, estate, corporate)
- Different statuses (vacant, occupied, tax delinquent)
- Some leads with notes and tags

This ensures all features can be tested properly.

---

## Automated Testing (Future)

We're working on automated test suites. Coming soon:
- Unit tests for each skill
- Integration tests
- Performance benchmarks
- Regression testing

---

**Happy Testing! 🧪**

Found all skills working? Give us a ⭐ on GitHub!

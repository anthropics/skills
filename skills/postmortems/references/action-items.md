# Action Item Categories and Guidelines

## Categories

Generate action items across these categories to ensure comprehensive coverage:

| Category | Question to Ask | Examples |
|----------|----------------|----------|
| **Investigate this incident** | "What happened to cause this incident and why?" | "Analyze logs from [timeframe] to identify all error patterns" |
| **Mitigate this incident** | "What immediate actions did we take to resolve this specific event?" | "Roll back deployment v1.2.3 to v1.2.2" |
| **Repair damage from this incident** | "How did we resolve immediate or collateral damage?" | "Restore corrupted user data from backup timestamped [date]" |
| **Detect future incidents** | "How can we decrease time to accurately detect similar failures?" | "Add alerting for all cases where this service returns >1% errors" |
| **Mitigate future incidents** | "How can we decrease severity/duration of future incidents like this?" | "Implement graceful degradation when database connections exceed 80% capacity" |
| **Prevent future incidents** | "How can we prevent a recurrence of this sort of failure?" | "Add automated pre-submit check for schema changes" |

## Quality Guidelines

Ensure each action item is:

- **Actionable**: Phrase as a sentence starting with a verb
- **Specific**: Define scope narrowly
- **Bounded**: Indicate how to tell when it's finished

**Example improvements:**
- ❌ "Investigate monitoring for this scenario"
- ✅ "Add alerting for all cases where this service returns >1% errors"

## Third-Party Dependencies

When incidents involve third-party services, use this framework:

1. **Did the 3rd party violate our expectations?**
   - Review and assess their RCA
   - Suggest adjusting expectations and increasing resilience
   - Identify alternative solutions if expectations are unacceptable

2. **Did the 3rd party meet expectations, but our service failed anyway?**
   - Identify where our service needs to increase resilience
   - Suggest specific resilience improvements

3. **Do we not have clear expectations?**
   - Help establish expectations with the 3rd party
   - Suggest how to share expectations with teams

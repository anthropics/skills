# Insider Threat Case Studies

## Case Study 1: The Perfect Candidate

### Background
A Web3 startup hired a senior developer through a popular job board. Resume showed:
- 8 years experience at recognizable companies
- Strong GitHub profile with active contributions
- Excellent technical interview performance

### Red Flags Missed
- References were "former colleagues" who were difficult to reach
- Claimed to be in Eastern Europe but online at unusual hours
- Preferred crypto payment "for tax reasons"
- Camera issues during interviews ("broken webcam")

### What Happened
- Developer gained access to deployment infrastructure
- After 4 months, submitted code with subtle vulnerability
- Vulnerability was later exploited, $2M stolen
- Investigation revealed multiple projects targeted by same group

### Lesson
Video verification and genuine reference checks would have revealed identity inconsistencies.

---

## Case Study 2: The Slow Play

### Background
A DeFi protocol hired a contractor for frontend work. Contractor was:
- Responsive and professional
- Delivered quality work on time
- Gradually given more access over 6 months

### Red Flags Missed
- Multiple contractors from same agency had similar writing style
- Payment routed through intermediary company
- Developer declined optional team retreat
- Never available for spontaneous calls

### What Happened
- Contractor introduced malicious code in routine update
- Code created backdoor activated by specific transaction
- $500K drained before detection
- IP analysis showed access from multiple Asian countries

### Lesson
Extended access shouldn't be automatic. Regular re-verification needed.

---

## Case Study 3: The Supply Chain Attack

### Background
A popular open-source library was maintained by a contributor who:
- Started with legitimate, small contributions
- Built trust over 18 months
- Eventually became maintainer

### Red Flags Missed
- Contributor identity never verified
- No video calls with other maintainers
- Contribution pattern changed once maintainer status gained

### What Happened
- Malicious code inserted in minor version update
- Affected downstream projects that auto-updated
- Multiple protocols compromised through dependency
- Millions in combined losses

### Lesson
Supply chain security requires identity verification even for open source contributors in sensitive positions.

---

## Case Study 4: Detection Success

### Background
A protocol implemented strict hiring practices after reading SEAL guidelines:
- Video interviews with ID verification
- Background checks through third party
- Reference calls to verified company numbers
- 90-day limited access period

### Detection
During hiring process:
- Candidate's ID didn't match video appearance
- Reference company had no record of employment
- Phone number country code mismatched claimed location
- Candidate withdrew when asked for additional verification

### Outcome
Threat avoided before access granted. Candidate likely moved to easier target.

---

## Common Patterns Across Cases

1. **Identity Obfuscation**: Stolen or fabricated identities with enough detail to pass surface checks
2. **Patience**: Willing to invest months building trust before acting
3. **Technical Competence**: Actual skills, not just social engineering
4. **Distributed Operations**: Multiple people may operate single identity
5. **Financial Routing**: Complex payment chains to obscure destination
6. **Targeting**: Focus on projects with significant treasury or TVL

## Effective Countermeasures

Based on successful detections:
- Live video verification catches identity fraud
- Independent reference verification reveals fabricated history
- Working hour analysis reveals timezone deception
- Code review catches malicious insertions
- Access limitations reduce blast radius
- Multiple verification points create defense in depth

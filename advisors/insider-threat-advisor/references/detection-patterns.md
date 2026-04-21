# DPRK IT Worker Detection Patterns

## Behavioral Patterns

### Communication Style
- Overly formal or stilted English
- Copy-paste responses that don't quite fit context
- Delayed responses during certain hours (handlers reviewing)
- Reluctance to hop on impromptu calls
- Preference for async-only communication

### Work Patterns
- Productivity spikes that don't align with claimed timezone
- Work submitted at unusual hours for claimed location
- Quality inconsistency (different people working on account)
- Avoidance of pair programming or live collaboration
- Resistance to screen sharing during work

### Technical Behaviors
- VPN or proxy usage (check IP geolocation)
- Multiple concurrent sessions from different locations
- Git commits with different author patterns
- Code style inconsistencies suggesting multiple authors
- Credential sharing indicators in logs

### Financial Red Flags
- Payment to countries with DPRK facilitator presence (China, Russia, Southeast Asia)
- Requests to change payment method mid-contract
- Multiple contractors with similar payment destinations
- Preference for cryptocurrency payments
- Requests to split payments across accounts

## Verification Techniques

### Identity Verification
1. Video call with camera on
2. Have them hold ID document on camera
3. Cross-reference with public profiles
4. Use identity verification services
5. Verify phone number country code matches claimed location

### Technical Verification
1. Check timezone of development environment
2. Analyze working hour patterns over time
3. Review IP addresses in access logs
4. Compare code style across submissions
5. Monitor for VPN/proxy indicators

### Reference Verification
1. Find references independently (don't just use provided contacts)
2. Call companies directly, not numbers on resume
3. Verify LinkedIn connections are real people
4. Check employment dates against public records
5. Ask specific questions only real colleagues would know

## Monitoring for Active Employees

### Access Logging
- Monitor access to sensitive repositories
- Track data download patterns
- Alert on access from new IPs/devices
- Review privileged action logs

### Code Review
- Extra scrutiny on security-sensitive code
- Watch for obfuscated sections
- Check for hardcoded credentials or backdoors
- Review dependency additions carefully

### Communication Monitoring
- Watch for external data sharing (where legally permitted)
- Monitor for credential/access sharing
- Alert on unusual after-hours access

## False Positive Considerations

Not every red flag means DPRK. Consider legitimate explanations:
- Digital nomads do work odd hours
- Some people prefer cameras off
- Non-native speakers may seem stilted
- Privacy-conscious people use VPNs

**Use multiple indicators**, not single red flags. Pattern of concerning behavior is more significant than isolated incidents.

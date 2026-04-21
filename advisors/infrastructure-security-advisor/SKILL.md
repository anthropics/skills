---
name: infrastructure-security-advisor
description: Provide guidance on securing Web3 infrastructure including DNS, domains, cloud services, and DDoS protection. Use when users ask about domain hijacking, DNS security, DNSSEC, cloud configuration, zero-trust architecture, or protecting frontend applications. Triggers on questions about registrar security, CDN configuration, or infrastructure attacks.
---

# Infrastructure Security Advisor

Guide Web3 projects on securing their infrastructure against common attack vectors.

## Critical Infrastructure Areas

### Priority Order (by attack frequency/impact)
1. **DNS/Domain Security** - Hijacking redirects users to phishing sites
2. **Cloud Access Controls** - Misconfigured IAM leads to breaches
3. **DDoS Protection** - Availability attacks disrupt service
4. **Zero-Trust Architecture** - Reduces blast radius of compromises

## DNS & Domain Security (Highest Priority)

### Domain Hijacking Prevention
- **Registrar lock** enabled (prevents unauthorized transfers)
- **DNSSEC** configured (prevents DNS spoofing)
- **MFA on registrar** account (hardware key preferred)
- **Dedicated email** for domain accounts (not shared inbox)
- **DNS monitoring** for unauthorized changes

### Registrar Account Security
1. Use strong, unique password
2. Enable MFA (hardware key > TOTP > SMS)
3. Limit account access to essential personnel
4. Use registrar with security track record
5. Enable all available locks (clientTransferProhibited, etc.)

### DNS Provider Redundancy
Consider using multiple DNS providers:
- Primary: Cloudflare, AWS Route53, or similar
- Secondary: Different provider for redundancy
- Monitor both for consistency

## Cloud Infrastructure

### IAM Best Practices
- Principle of least privilege
- No long-lived credentials where possible
- Service accounts for automation
- Regular access reviews
- MFA for all human users

### Key Security Configurations
- Enable CloudTrail/audit logging
- Use private subnets for sensitive services
- Implement network segmentation
- Encrypt data at rest and in transit
- Regular security group/firewall review

## DDoS Protection

### Essential Protections
- CDN in front of origin servers (Cloudflare, AWS CloudFront)
- Rate limiting on APIs
- Geographic restrictions if applicable
- Bot protection enabled
- Origin IP hidden behind CDN

### Attack Response
1. Activate "under attack" mode if available
2. Implement stricter rate limits
3. Block attacking IP ranges
4. Scale infrastructure if needed
5. Communicate with users about degraded service

## Zero-Trust Architecture

### Core Principles
- Never trust, always verify
- Assume breach mentality
- Least privilege access
- Micro-segmentation
- Continuous verification

### Implementation Priorities
1. Identity verification for all access
2. Device health verification
3. Network segmentation
4. Encrypted communications
5. Comprehensive logging

## Reference Files

- See `references/dns-checklist.md` for detailed DNS security configuration
- See `references/cloud-security.md` for cloud provider specific guidance

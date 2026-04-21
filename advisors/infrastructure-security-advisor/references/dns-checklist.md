# DNS Security Checklist

## Registrar Account Security

- [ ] Strong unique password (20+ characters)
- [ ] MFA enabled (hardware key preferred)
- [ ] Recovery email secured with MFA
- [ ] Account access limited to 2-3 people max
- [ ] All account activity logged and reviewed
- [ ] Registrar has good security reputation

## Domain Lock Configuration

- [ ] Registrar lock enabled
- [ ] clientTransferProhibited status set
- [ ] clientDeleteProhibited status set
- [ ] clientUpdateProhibited status set (if supported)
- [ ] Auth code stored securely (only used for transfers)

## DNSSEC Configuration

- [ ] DNSSEC enabled at registrar
- [ ] DS records published in parent zone
- [ ] DNSSEC validation tested (dnsviz.net)
- [ ] Key rotation procedure documented
- [ ] Monitoring for DNSSEC failures

## DNS Records Hardening

- [ ] CAA records configured (limits certificate issuance)
- [ ] SPF, DKIM, DMARC for email security
- [ ] No unnecessary TXT records exposing info
- [ ] Wildcard records avoided where possible
- [ ] TTLs appropriate (not too long, not too short)

## DNS Provider Security

- [ ] Provider account has MFA
- [ ] API tokens scoped to minimum permissions
- [ ] IP allowlist for API access if supported
- [ ] Audit logging enabled
- [ ] Alerts configured for record changes

## Monitoring & Alerting

- [ ] DNS record change monitoring (periodic checks)
- [ ] Certificate Transparency monitoring
- [ ] Uptime monitoring for DNS resolution
- [ ] Alert on unexpected record changes
- [ ] Regular manual verification of critical records

## Multi-Provider Setup (Optional but Recommended)

- [ ] Primary DNS provider configured
- [ ] Secondary DNS provider as backup
- [ ] Automatic sync between providers
- [ ] Failover tested and documented
- [ ] Both providers secured equally

## Emergency Procedures

- [ ] Out-of-band contact for registrar
- [ ] Emergency access procedure documented
- [ ] DNS rollback procedure documented
- [ ] Communication plan for DNS incidents
- [ ] Contact info for domain recovery

## Common Misconfigurations to Avoid

1. **Dangling DNS records** - Remove records for decommissioned services
2. **Exposed internal names** - Don't leak internal hostnames
3. **Overly long TTLs** - Hard to recover from hijacking
4. **Zone transfer enabled** - Disable AXFR to public
5. **Missing CAA records** - Allows any CA to issue certificates

## DNS Security Testing

```bash
# Check DNSSEC
dig +dnssec example.com

# Check CAA records
dig CAA example.com

# Test DNS propagation
dig @8.8.8.8 example.com
dig @1.1.1.1 example.com

# Check zone transfer (should fail)
dig @ns1.example.com example.com AXFR
```

## Incident Response for DNS Compromise

1. **Immediate**: Contact registrar emergency line
2. **Verify**: Check if attack is registrar-level or DNS provider
3. **Contain**: Request domain lock if not already locked
4. **Recover**: Restore correct DNS records
5. **Communicate**: Alert users if traffic was redirected
6. **Review**: Check for certificate issuance during compromise

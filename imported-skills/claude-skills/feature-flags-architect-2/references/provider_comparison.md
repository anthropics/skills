# Provider comparison

Five mainstream providers + DIY. Pick based on flag count, targeting needs, compliance, and self-hosting requirements.

## At-a-glance matrix

| Provider | Flag count sweet spot | Targeting | A/B testing | Audit log | Self-host | OSS | Pricing model |
|---|---|---|---|---|---|---|---|
| **LaunchDarkly** | 100+ | Best-in-class | Yes (Galaxy) | Full SOC2 audit trail | Edge SDK only | No | Per-MAU, expensive |
| **GrowthBook** | 20-500 | Good | Yes (built-in) | Yes | Yes (Docker/k8s) | Yes (MIT) | Free OSS + Cloud per-MAU |
| **Statsig** | 50-500 | Good | Best-in-class | Yes (paid) | No | No | Free tier (1M events), then per-MAU |
| **Unleash** | 10-200 | Good | Limited | Yes (Enterprise) | Yes (Docker/k8s) | Yes (Apache 2) | Free OSS + Hosted/Enterprise |
| **Flipt** | 5-100 | Basic | No | Limited | Yes (Docker/k8s) | Yes (MIT) | OSS only |
| **DIY** | <50 | None to basic | None | Whatever you build | Always | N/A | None |

## When to choose each

### LaunchDarkly

Choose if:
- Enterprise team with 100+ flags across many services
- Compliance requires SOC2 / ISO 27001 / FedRAMP audit logs
- Need fine-grained targeting (cohorts, custom attributes, percentages by attribute)
- Need experimentation + targeting + audit in one platform
- Budget for enterprise tooling ($20-100k/year typical)

Avoid if:
- Small team / <50 flags (overkill)
- Strict data residency (no on-prem; relays only)
- Low budget

### GrowthBook

Choose if:
- Mid-market team that wants OSS option for self-hosting
- Need built-in A/B testing with proper stats (frequentist + Bayesian)
- Want SQL-based experimentation (define metrics from your warehouse)
- Self-host on k8s or run their hosted Cloud

Avoid if:
- Need real-time targeting at edge (use LD or Statsig)
- Need enterprise audit features (Cloud only)

### Statsig

Choose if:
- Growth/product team for whom experimentation is the core use
- Need advanced stats (CUPED, sequential testing)
- Want generous free tier (good for early-stage)
- Want best-in-class metric library and platform-side experimentation logic

Avoid if:
- Strict data residency / self-host requirement (no on-prem option)
- Don't need experimentation, just toggles (overkill)

### Unleash

Choose if:
- OSS-first culture; want to self-host
- Dev-friendly with good SDKs and a clean API
- Don't need full A/B testing platform
- Need Open Source license for compliance (Apache 2)

Avoid if:
- Need experimentation + stats out of the box
- Need enterprise-grade audit (Enterprise tier only)

### Flipt

Choose if:
- Lightweight needs, <100 flags
- k8s-native (Flipt is operator-friendly)
- Want pure OSS, no commercial component
- Don't need A/B testing

Avoid if:
- Need targeting beyond simple boolean rules
- Need experimentation
- Need analytics or audit features

### DIY (env vars / config file)

Choose if:
- <50 flags total
- No targeting beyond `enabled: true/false`
- No A/B testing needs
- Want zero external dependencies
- Strict cost control

Implementation:
```yaml
# config/flags.yaml
flags:
  new-checkout: { enabled: true, owner: jane@team }
  payment-v2:   { enabled: false, owner: bob@team, kill_switch: PagerDuty alert "payment-v2 SEV1" }
```

Or env-var based:
```bash
FLAG_NEW_CHECKOUT=true
FLAG_PAYMENT_V2=false
```

Avoid if:
- Flag count growing past 50
- Need percentage rollouts (you'll re-implement provider logic poorly)
- Need audit log (compliance)
- Multiple teams / multiple deploy cadences

## Cost rule of thumb

| Team stage | Typical monthly cost |
|---|---|
| Pre-seed / solo | $0 (DIY or OSS) |
| Seed (Series A) | $0-200 (Statsig free tier, Unleash OSS) |
| Series B-C | $500-3,000 (GrowthBook Cloud, Unleash Pro) |
| Series D+ / Enterprise | $5,000-20,000+ (LaunchDarkly, Statsig Pro, Unleash Enterprise) |

## Migration paths

Easy migrations:
- DIY → Unleash / Flipt (similar simple model)
- Unleash ↔ GrowthBook (similar feature surface)

Hard migrations:
- LaunchDarkly → anywhere (proprietary targeting language)
- Statsig → anywhere (proprietary experimentation logic)

**Lock-in mitigation:** Wrap your provider behind an interface in code:
```ts
interface FlagProvider {
  isEnabled(name: string, context?: UserContext): boolean;
  getValue<T>(name: string, defaultValue: T, context?: UserContext): T;
}
```
Swap providers by writing a new adapter, not by rewriting every call site.

## Build-vs-buy threshold

Buy a provider when:
- Flag count > 50
- Multiple teams need to manage flags independently
- Targeting needs include percentages, cohorts, or custom attributes
- Compliance requires audit log
- Need real-time updates without redeploy

Build (DIY) when:
- All of the above are NO

## Selection checklist

Before signing a contract:
- [ ] Estimate flag count over 12 months
- [ ] List required targeting dimensions (user/account/geo/%/custom)
- [ ] Confirm SDK availability for every language in your stack
- [ ] Check edge latency (p99 < 50ms for prod)
- [ ] Verify failure mode if provider is unreachable (default-to-safe)
- [ ] Confirm SOC2 / data residency if needed
- [ ] Run a 30-day proof-of-concept; measure actual cost at projected MAU

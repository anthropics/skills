export const dnsFlowDiagram = `flowchart TD
    Start([User types:example.com]) --> Cache{CheckCache?}
    
    Cache -->|Found| Fast[Return IP instantly93.184.216.34]
    Cache -->|Not Found| Recursive[Your ISP DNSRecursive Resolver]
    
    Recursive -->|1. Where is .com?| Root[Root Server.]
    Root -->|2. Ask TLD| Recursive
    
    Recursive -->|3. Where is example.com?| TLD[TLD Server.com]
    TLD -->|4. Ask Authoritative| Recursive
    
    Recursive -->|5. What's the IP?| Auth[Authoritative Serverexample.com]
    Auth -->|6. IP: 93.184.216.34TTL: 24h| Recursive
    
    Recursive -->|7. Validated & Cached| Result[Return IP93.184.216.34]
    
    Fast --> Connect([Connect to Website])
    Result --> Connect
    
    style Start fill:#e1f5ff
    style Connect fill:#d4edda
    style Root fill:#fff3cd
    style TLD fill:#fff3cd
    style Auth fill:#d1ecf1
    style Recursive fill:#e7e7ff
    style Fast fill:#a8e6cf
    style Cache fill:#ffeaa7`;

# DNS Basics & Common Attacks

## How DNS Resolution Works

When users type your domain, their request may traverse multiple trust points (flows vary by resolver caching, stub resolver config, and provider):
1. Local device cache
2. ISP/recursive DNS resolver
3. Root nameservers
4. TLD registry servers
5. Your authoritative nameservers

Each step represents a potential attack surface where responses can be intercepted, modified, or poisoned. This multi-step process creates numerous opportunities for attackers to redirect users to malicious sites while their browser still shows the correct domain name.

## Common Attack Vectors

- Social Engineering at Registrars: Attackers convince/bribe support staff they're legitimate owners using publicly available information
- Expired Domain Sniping: Domains that expire enter a grace period before becoming publicly available to anyone (note: grace/redemption periods differ per TLD)
- DNS Hijacking: Unauthorized changes to DNS records redirecting traffic to malicious servers
- Email Interception (MX tampering): Password reset attacks and communication interception
- DNS Tunneling: Encoding data within DNS queries for covert communication channels, often used for data exfiltration
- DNS Cache Poisoning: Injecting forged responses into a resolver's cache to redirect subsequent queries

---


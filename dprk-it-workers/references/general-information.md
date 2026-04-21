# General Information

## What is an insider threat? Who are DPRK IT Workers?

1. An insider threat refers to the risk posed by individuals within an organization who misuse their authorized access
    to compromise the organization's security. This misuse can involve malicious actions like data theft or sabotage, but
    also unintentional actions like negligence (e.g. ignoring security updates) or accidents (e.g. sending sensitive
    document to the wrong email address) leading to security breaches and/or data leaks.
2. DPRK IT workers are individuals from North Korea (the Democratic People's Republic of Korea) who engage in remote IT
    work for foreign companies, often using false identities. Their work, while often appearing legitimate, is a source of
    revenue for the North Korean regime, may be involved in malicious activities, and constitutes a serious violation of
    international sanctions to send payments to North Korea. **"DPRK IT Workers" are synonymous with an "insider threat."**
3. Read: [OFAC's North Korea Information Technology Workers
    Advisory](https://ofac.treasury.gov/recent-actions/20220516)
4. Read: [Google's advisory on DPRK IT
    Workers](https://cloud.google.com/blog/topics/threat-intelligence/mitigating-dprk-it-worker-threat)

## Operational structure and short history of DPRK IT Workers

1. North Korean IT workers, operating both within the DPRK and abroad, are a significant source of revenue for the
    country's regime, particularly for its weapons programs. **They engage in various IT roles (but are not limited to these
    roles!), often disguising their identity and location to secure freelance contracts and generate income that is
    remitted back to North Korea.** These workers are primarily based in China and Russia, with some in other parts of Asia,
    Africa, and Latin America. **North Koreans are also observed to run a network of 'facilitators' (or local accomplices)
    to help them cover their identities and facilitate remote employment. The facilitator lends his or hers digital and
    physical identity in exchange for compensation from the DPRK IT Workers.**
2. Reports of North Korean IT workers operating internationally began to surface around the mid-2010s, with a growing
    awareness of their role in generating revenue for the regime. The number of DPRK IT workers increased, with a wider
    geographical spread and a diversification of their activities from the late-2010s to the present.
3. Read: [Google's North Korean Cyber Structure and
    Alignment](https://cloud.google.com/blog/topics/threat-intelligence/north-korea-cyber-structure-alignment-2023)
4. Read: [Google's advisory on DPRK IT Workers expanding scope and
scale](https://cloud.google.com/blog/topics/threat-intelligence/dprk-it-workers-expanding-scope-scale)

## What are the goals of DPRK IT Workers?

1. Generating stable revenue for the North Korean regime through remote IT work.
2. Building support networks for North Korean IT-related operations (mules and money laundering).
3. Gaining access to Western companies technology, infrastructure, and identities (both personal and company, digital
    and physical).
4. Exfiltrating company secrets (intentionally and unintentionally).
5. Extortion (ransomware and blackmail).
6. Avoiding sanctions (North Korean entities are barred from receiving any form of payment from Western countries).
7. Hacking (establishing permanent access to infrastructure in which they can gain a foothold or infiltrate).
8. Malware (infecting high-value targets for future theft).
9. Read: [DPRK IT Workers pushing malicious code and stealing 1.3M](https://x.com/zachxbt/status/1824047425822310580)
10. Read: [Highlights from the UN Security Council on DPRK IT
Workers](https://x.com/tayvano_/status/1777911893224808911)

## How many DPRK IT Workers are there?

The exact number is hard to estimate. DPRK IT Workers operate in separate 'cells' (different teams distributed over
different locations, often without any direct contact with one another), and their organizational structure is flexible
(even chaotic). Some workers focus exclusively on the blockchain space, while others are never seen applying outside of
Fortune 500 companies. Estimates by different companies and government agencies vary between 2,000 and 15,000 in total.
However, it's worth noting that this number includes multiple identities being re-used by the same actor or inactive
accounts. **We estimate that about 3-5% of all Web3 developers are North Korean, and at any given time, there are at
least 200-300 DPRK-related accounts actively seeking employment in Web3 companies.**

## Average DPRK IT Worker Profile

In the following sections of this framework, we will discuss more advanced methods for detecting deeply nested DPRK IT
Workers who may avoid the usual heuristics. However, it is still important to review the most common indicators of North
Korean insider threats. If you suspect any of your contributors or have received a report regarding one, this set of
questions can help you evaluate if you are dealing with a typical North Korean operative.

1. **Did you meet your contributor in real life?**
     1. Yes - Significantly lowers the chance that the contributor is North Korean.
     2. No - Red flag.
2. **Is your contributor an Asian man in his 20s or 30s?**
     1. Yes - Red flag.
     2. No - Lowers the chance that the contributor is North Korean, but they could still be a 'facilitator'.
3. **Does your contributor avoid real-life meetings?**
     1. Yes - Red flag.
     2. No - Even if they agree to a meeting, North Koreans will often try to postpone it indefinitely.
4. **How often do you sync with your contributor, and is their video on during calls?**
     1. Often, with video on - Lowers the chance that the contributor is North Korean.
     2. Rarely, or with video off - Red flag. North Koreans will try to appear 'independent' and focus only on technical
        output.
5. **Does your contributor consistently try to recommend someone else for the job? Are those recommendations also for
    Asian men in their 20s or 30s?**
     1. Yes - North Koreans will try to place other North Koreans in your organization.
     2. No - Lowers the chance that the contributor is North Korean.
6. **Is your Asian contributor's name 'westernized' (e.g., Victor Lee, James Kano) or extremely generic/popular (e.g.,
    Scott Brown, James Smith)?**
     1. Yes - North Koreans have a tendency to use generic, pre-generated fake names.
     2. No - Lowers the chance that the contributor is North Korean.
7. **Does the KYC documentation provided by your Asian contributor show an unorthodox combination of nationality and
    physical appearance (e.g., an Asian man living in Indonesia with a Latin American passport)?**
     1. Yes - North Koreans often repurpose stolen identities to fit their fabricated backstory.
     2. No - Lowers the chance that the contributor is North Korean.
8. **Does your contributor have poor English communication skills, despite claiming to live in the US?**
     1. Yes - It is atypical for someone with a US passport to have poor English skills in an IT job.
     2. No - Lowers the chance that the contributor is North Korean.

We cover more detailed indicators in the section [**Techniques, Tactics, and
Procedures**](/dprk-it-workers/techniques-tactics-and-procedures)

---


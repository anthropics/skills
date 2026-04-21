# Mitigating DPRK IT Workers

This section discusses ways you can harden your organization against DPRK IT Workers, both before and after a potential
hiring. All of the strategies covered in the prior section, [**Techniques, Tactics, and
Procedures**](/dprk-it-workers/techniques-tactics-and-procedures), still apply but serve a more 'active' role to
identify DPRK IT Workers during recruiting or within your organization. Here, we will discuss mitigation strategies that
limit the effects of a DPRK IT Worker infiltration and what you should do after identifying a successful infiltration.

## Hardening your hiring processes

1. Apply all the steps from the sections [Am I Interviewing a DPRK IT
    Worker?](/dprk-it-workers/techniques-tactics-and-procedures#am-i-interviewing-a-dprk-it-worker) and [Did I hire a DPRK
    IT Worker?](/dprk-it-workers/techniques-tactics-and-procedures#did-i-hire-a-dprk-it-worker). **It's important to educate
    all of your non-DPRK employees on these points, especially people responsible for hiring, developer relations, talent
    hunting, and community management.**
2. Introduce a culture of background checks. Do not take a prospective developer's claims at face value. **Even the
    most basic OSINT check can often discover deep inconsistencies. Check GitHub commit history, check Twitter history, and
    Google the full name of the developer.**
     1. Is the work experience claimed in the CV reflected on GitHub?
     2. Does the potential employee indicate any physical presence anywhere?
     3. Is the potential employee writing non-AI-generated posts and replying to anything other than job offers on
        Twitter?
     4. Did you find any name collisions after searching for the potential employee's name in Google?
     5. Did you check the potential employee's nickname in Google? Maybe they have already appeared as a threat actor in
        a past report?
     6. **Remember the best discovery rule:** You're looking for misrepresentations, mismatches, and obfuscation, not
        for North Koreans specifically. Tick your boxes on the first three and only then proceed to decide if you're potentially
        dealing with a North Korean.
3. **Do not try to undercut developer market salaries.** DPRK IT Workers will always accept low-ball offers without
    much hesitation. If you're looking for a cheap hire, you are at a higher chance of hiring a DPRK IT Worker.
4. **ALWAYS perform your own due diligence on new remote employees.** Do not settle for recommendations from third
    parties; they could be victims themselves.
5. You could ask about North Korea on call and observe the reaction. There's a so-called "F**k Kim Jong Un" test, where
    interviewer is asking to repeat the phrase and North Koreans are banned from saying it and they drop the call
    immediately. Obviously, it won't be effective for 'facilitators' but it will most likely be effective for North Koreans
    themselves. Do not rely on it as a panacea.
6. Regardless of our tips of not focusing on "Asian man in his 20-30s" that particular appearance is still the most
    common (If not cloaked under the generative AI). Similarly, Korean-English accents.

## Hardening your organization

1. Define and implement tight access control rules for all of your employees, especially remote ones. Avoid giving
    privileged access to workers who did not pass 100% of the tests and filtering criteria for DPRK IT Workers (all the
    points already discussed). Specific examples of privileged access include:
     1. Do not give admin permissions to your GitHub organization and repositories, including for build releases, adding
        members, and repository settings.
     2. Do not give publishing permissions on any package managers. The publishers of your packages are a critical
        supply chain risk; they need to be 100% vetted.
     3. Do not add your remote employees as multisignature wallet signers. The signer role should be reserved only for
        high-trust individuals, not based on the dedication of the developer you are working with.
     4. Do not give unlimited access to cloud instances. Scope permissions to the minimal access required for each
        individual or team, including setting minimal expiration times for access tokens (e.g. access tokens should expire
        within hours, not weeks).
2. Define a lead developer - a highly trusted individual you've met in real life and are sure of their background - as
    the code reviewer, publisher, signer, and image builder. This individual's role should be to double-check all of the
    remote workers' work and actions within your organization at all times. Make sure the lead developer is not a DPRK IT
    Worker.
3. Silo your remote workers from the most critical infrastructure. If you choose to provision access to such
    infrastructure, always create a threat model to understand the 'worst-case' scenario and potential mitigation
    approaches.
4. Monitor your logs for IP addresses, user sessions, and timestamped access. Monitor your remote contributors' actions
    for any sudden changes (identity changes) and potential secrets leaks through their private accounts. You can obtain
    such information from Google, Slack or Github Workspaces, depending on your organization setup and tiers.
5. **DO NOT allow hired contributors to use throwaway Github accounts for the work at your company!** It's part of the
    DPRK IT Worker tactics to save their main accounts from being discovered.
6. If your project allows, it may be beneficial to establish a public codebase on GitHub and have your remote workers
    make at least *some* public contributions related to your project. If all of your codebase is supposed to stay private,
    at least list all of the contributors (CODEOWNERS) in a special repository created only for such purpose. Security
    researchers like SEAL911 scan such public codebases and will notify you privately if they suspect DPRK IT Workers are
    contributing to your project.

## I hired a DPRK IT Worker. What now?

1. Contact security professionals if you're unable to handle the situation alone. You can reach out to SEAL911
    (@seal_911_bot on Telegram).
2. **You do not need to end the engagement abruptly. It's important to maintain a facade while you deal with access
    revocation and mitigate any immediate risks to your organization.** Act normally, but start preparing an actionable plan
    immediately and aim to remove the DPRK IT Worker within the next few days at most. If your organization is properly
    siloed from insider threats, you shouldn't have much of an issue firing the worker almost immediately after
    conducting a post-mortem review.
3. **Check if you did not hire more than one DPRK IT Worker. In the majority of cases, we find more DPRK IT Workers
    within the same organization.** They do not always come as a recommendation from an already-discovered DPRK IT Worker;
    they simply already know how to abuse your hiring process.
4. At the same time, **you should immediately cease any further payments to the DPRK IT Worker. It's illegal.** You can
    cite temporary financial issues as the reason for the delay if confronted by the worker and you still need a bit of
    time to deal with the situation.
5. List all infrastructure endpoints the DPRK IT Worker had access to, both sensitive and not. Useful, for the next
    steps.
6. Review the current and past work of the accounts in question. The code does not necessarily need to be malicious,
    but it can be of overall poor quality. **Pay extra attention to added dependencies or edited CI/CD files.**
7. Review the permissions that these actors have or had in your organization. **Revoke them.**
8. **Review all of the files and links previously provided by the DPRK IT Worker and who opened them.** The issue may
    extend beyond your technical workers. Look back to see if you did not potentially run malware-infested code or give them
    remote desktop access to your or your developers' machines.
9. Set up a final confirmation call after all access is revoked and you are certain your organization is safe from any
    insider threats. **Attempt to perform KYC under some pretense. Do not settle for document scans, as these are easily
    obtainable.** Insist on a "video call" KYC, where the actor must show the physical document they previously provided
    next to their face.
10. Attempt to geolocate them. Send a document that tracks the IP address used to open it. Look for VPN usage or IP
    addresses in the DPRK/Eastern Russian range.
11. Collect all on-chain/payroll data on funds transferred to the actor. If an actor is confirmed as DPRK-related, you
    will be required to file a Suspicious Activity Report (SAR). We would appreciate you sharing this data with
    [SEAL911](https://www.securityalliance.org/) later for public security reasons and future investigations. The data will
    remain private.
12. You do not need to inform the DPRK IT Worker about the actual reasons for termination. You can cite downsizing, poor
    performance, lack of cultural fit, or any other reason.
13. **In the post-mortem phase, you will need to halt all development on the affected infrastructure.** For companies
    that hired a DPRK IT Worker as a "Core Engineer," this may sometimes mean several weeks of re-auditing all code and
    infrastructure. **You should stop and do it.** At the same time, build a threat model to prevent the situation from
    recurring and to limit its effects if it does happen again. You can remove the DPRK IT Worker's code from your codebase.
    **DPRK IT Workers will claim this code as part of their work experience in their future job searches.**
    The decision is ultimately yours. While not removing the code helps security researchers like those at SEAL911
    track these workers, our recommendation is to remove it to protect your project and deny adding credibility to
    DPRK IT Worker.

## Data collection

1. You should collect the following data before firing the DPRK IT Worker. This data will help organizations like SEAL
with future mitigation and the discovery of other actors.
     1. Full Legal Name
     2. Phone
     3. Email(s)
     4. Location (City/State)
     5. LinkedIn
     6. Telegram/Discord
     7. GitHub
     8. Copy of Resume
     9. Date Hired
     10. Sourcing (Where were they hired from? Telegram, Staffing, Recruiter, etc.)
     11. Company Email (Yes/No)
     12. IP addresses (from email or any other sources at your disposal)
     13. Managed Laptop (Yes/No)
             1. Shipment address (for the laptop or other items)
     14. KYC data (ID/Passport/Bills document scans)
     15. Photos/Screenshots (physical appearance, potentially from a video call)
     16. Payment data **(Extremely important!)**
             1. On-chain addresses provided for payment
             2. Bank data
     17. Did they refer anyone else?
     18. Were they referred by someone else?

## Overview of risks to your organization

1. **Defrauding the company:** The company is paying someone whose identity they do not know.
2. **Subpar operational security:** DPRK IT workers share credentials among themselves in open channels, have a poor
    command of Git, and unintentionally or intentionally leak the access they are granted to third parties.
3. **Extortion:** They may try to extort more money after a job is finished.
4. **Future hacking activities:** They may use the knowledge gained for future hacking activities.
5. **Sanctions violations:** The DPRK is a sanctioned entity. No company can legally transfer funds to DPRK-related
    operations.
6. **Contribution to the North Korean Military:** DPRK IT worker salaries directly contribute to the Military Ministry
of North Korea. The workers do not keep the salaries for themselves.

---


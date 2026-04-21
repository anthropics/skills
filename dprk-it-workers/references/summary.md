# Summary

* **Who are DPRK IT Workers?** They are North Korean individuals, often operating from abroad (primarily China and
Russia), who use fraudulent identities to secure remote IT jobs. Their primary goal is to generate revenue for the North
Korean regime, which may involve legitimate work but also opens the door to espionage, data theft, extortion, and
future hacking activities.

* **How to Spot DPRK IT Workers During Hiring:**
  * Focus on detecting **fraud and misrepresentation**, not stereotypes. Look for inconsistencies across their CV,
    digital profiles, and interview answers.
  * During video interviews, insist the camera is on. Watch for AI-generated faces, obscured or generic backgrounds,
    and an inability to answer small-talk questions related to their claimed location or nationality.

  * Scrutinize their GitHub profile for red flags like a recent account creation date with years of "faked" commit
    history, "copied" repositories from legitimate projects, spam-like contributions, or interactions with other
    suspicious
    accounts.
  * Check their social media (LinkedIn, Twitter) for a lack of personal photos, a history of job-begging posts, and
    no evidence of a physical presence at conferences or events.
  * Be wary of highly unorthodox identity combinations, such as an Asian individual living in one country while
    providing KYC documents from a completely different continent.
* **How to Verify an Existing Employee:**
  * Watch for behavioral patterns like consistently avoiding in-person meetings with repeated excuses or work
    patterns that don't match their claimed time zone.
  * Audit workspace logs for suspicious IP addresses (VPNs, proxies, known sanctioned regions).
  * Be on high alert if an employee suddenly changes their name or GitHub handle, or deletes social media accounts,
    as this often happens after being discovered elsewhere.
  * Verify their claimed work history independently. Be cautious if they recommend other candidates, as they often
    leverage their position to bring in more DPRK operatives.
* **How to Harden Your Organization:**
  * Implement a "least privilege" principle for access control. New and remote employees should not have admin
    rights, permission to publish packages, or be signers on multisig wallets.
  * Appoint a trusted, fully-vetted individual to review all code and actions from remote contributors before they
    are merged or deployed.
  * Perform your own due diligence on all remote hires. Do not rely solely on third-party recruiters or
    recommendations, as they can also be victims.
  * Avoid the temptation to hire based on the lowest salary offer, as DPRK IT workers often work at a significant
    discount.
* **What to Do After Discovering a DPRK IT Worker:**
  * **Do not fire them immediately.** Maintain a normal appearance to avoid tipping them off while you secure your
    organization.
  * **Immediately stop all payments**, as funding them is a sanctions violation. If confronted, use a pretext like
    "financial issues" to buy time.
  * **Systematically revoke all access** to code repositories, cloud infrastructure, and internal systems. At the
    same time, collect all available data (KYC docs, crypto addresses, emails, resumes) for reporting.
  * **Conduct a full security audit** of all their code contributions, paying close attention to dependencies, build
    files (CI/CD), and potential backdoors.
  * Once your systems are secure, terminate their contract using a business-related reason (e.g., downsizing, change
    in direction) and report the incident to law enforcement.

---


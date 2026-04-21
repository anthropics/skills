# Case Studies

Here are a few deviations from the usual DPRK IT Worker patterns. **As mentioned a few times already, the goal is to
always be open-minded about threat actor tactics.** They are known to evolve and adapt while also pushing their methods
further. The examples below are anonymized, but they are real cases we have encountered in the past:

## Story 1

**Background:** A GitHub profile created in 2013, with no flagged "copied repositories" (indicating original code), an
active and verified Twitter account from 2012, and no history of nickname changes on any platform. The user claimed to
be Japanese, which was reflected in his posts and 10+ years of digital activity. The nicknames were "relevant" to
Web3/Blockchain (e.g., using a "0x" prefix or "sol" in the name). A Rust developer with experience in Solana was looking
to get hired by a Solana project.

**Conclusion:** This was a DPRK IT Worker, confirmed by independent sources who had also been "spammed" by the same
actor. The most likely reason for avoiding most software flags was a "stolen" account. DPRK operatives managed to get
their hands on the GitHub and Twitter handles of a Japanese citizen, which had been lying dormant without ANY activity
for 10+ years. They then proceeded to build a history on these accounts for almost two years before starting to apply
for jobs and messaging other developers. It's worth noting that no event history was present for this GitHub account, as
the original owner had never used it after signing up. This allowed them to build a "perfect" dummy history with no
event data present in the GitHub Archive. This absence of data, along with a significant gap in Twitter activity between
2013 and 2022, contributed to flagging this particular actor.

## Story 2

**Background:** An actor who had worked for three years at a popular security company. (An example of a perfect
backstory for future employment.) The actor was usually delegated auxiliary tasks, which he completed diligently and on
time. He was reluctant to accept promotions or on-site invitations, citing his own business as the reason. The company
was fine with this, as he was an auxiliary worker. His GitHub profile was created in 2021 and had a single, yet
consistent, name change. The actor used his GitHub account only for work at that company and did not maintain any social
media profiles. There was no overly informative README/About page, no avatar, and he consistently used a single Gmail
address.

**Conclusion:** This was a DPRK IT Worker. By cross-referencing our existing database and performing an extremely deep
analysis of commits from actors we suspected were connected to him, we finally found his old nickname associated with
two commits to an already known -but old and inactive - account of a known DPRK IT Worker. Confirmation was only
possible through a video call with the company's participation. (On-call KYC and a few other tactics were used; the
threat actor decided to abandon the call and delete his profiles.)

## Story 3

**Background:** An actor with a consistent identity across all relevant platforms (GitHub, Twitter, LinkedIn). He was
referred by a legitimate company and had already been working with the affected company for a year. He claimed to be
based in Canada (using an IP from a Laptop Farm), spoke good English, performed his tasks diligently and on time (the
company claimed he was selected as a top candidate), had no issues with video calls, and used his own physical
appearance (no Gen-AI).

**Conclusion:** This was a DPRK IT Worker. **We scanned contributors to a few of his repositories and found that all of
them were high-confidence DPRK IT Workers. From their profiles, we managed to pinpoint a history of identity rotations
(changes in legal names).** The final confirmation was only possible with the company's participation. The actor was
"cut off" from access to company infrastructure and given the pretext of a potential breach the company suspected. This
gave them a reason to perform additional KYC - "to make sure the (suspected) dev account is not compromised." The actor
was asked to go outside his claimed location and take a "selfie" in front of the house where he supposedly lived. He
refused and resigned immediately, blocking all accounts.

---


# Techniques, Tactics, and Procedures

This section focuses on avoiding, discovering, and confirming the threat of DPRK IT Workers to your organization.
The sections dedicated to answering the questions "Am I interviewing a DPRK IT Worker?" and "Did I hire a DPRK IT
Worker?" are interchangeable and both provide strategy outlines for avoiding, discovering, and confirming DPRK-related
insider threats. Your organization can use tips from these sections to identify a DPRK IT Worker before you hire them,
as well as to identify them after you have made the mistake of hiring one.

This section focuses on dealing with emergent situations to identify potential DPRK IT workers who are attempting
to or already have infiltrated your organization. In the next section,
([**Mitigating DPRK IT Workers**](/dprk-it-workers/mitigating-dprk-it-workers)), we will discuss strategies to harden
your organization to minimize both the impact and the chances of infiltration and how to deal with the fallout of
hiring a DPRK IT Worker.

## How can DPRK IT Workers find a job in your company?

1. There is no single established channel through which a DPRK IT Worker can approach your company.
    Applying with an impressive CV and GitHub portfolio through a public channel (LinkedIn/Job Portal) is common;
    however, we have often observed alternative routes, such as:
     1. **Direct outreach to CEO/CTO.** They are persistent until clearly denied the opportunity, and even then,
        the actor may change their identity and try again.
     2. **Initiating contact through open-source contributions.** An actor will submit valid Pull Requests to your
        repositories and use this as a way to request a job interview.
     3. **Recommendation.** A worker will come recommended by another DPRK IT Worker or by a company they previously
        infiltrated (where the company may or may not be aware the employee is a DPRK IT Worker).
     4. **Tech recruiters.** Recruiters often prioritize evaluating skillsets over performing background checks.
        DPRK IT Workers can appear on their radar and be unwittingly pushed by a legitimate tech recruiter to your company.
     5. **Bounty/Hackathon participation.** DPRK IT Workers look for ANY source of revenue, no matter how small or
        large. If your company runs free-for-all bounty systems, it's extremely likely that some of the contributors are
        DPRK IT Workers.
     6. **Hired through a "dev shop."** If you recruit your employees through an outsourcing agency, you need to
        ensure their vetting process is appropriate. The outsourcing agency itself can be a victim of DPRK IT Worker
        infiltration.
2. The bottom line is that there is no single "safe" remote recruitment channel. You should vet your potential
    employees independently and **look beyond their skillset, which can often be impressive.** We have observed
    DPRK IT Workers joining companies by utilizing all the channels mentioned above. Establish a high-quality hiring
    process to avoid recruiting DPRK IT Workers; do not blindly rely on outsourced solutions.

## Am I Interviewing a DPRK IT Worker?

1. The list below can serve as a guide for avoiding hiring a DPRK IT Worker and as an exit-interview guide for
    verifying if an employee is a DPRK IT Worker.
2. Before discussing the heuristics: **Don't over-focus on stereotypical DPRK IT worker characteristics, such as being
    an Asian male in their 20s or 30s, using specific headphones, or obscuring their background. What you are looking for
    is evidence of misrepresentation and fraud. Job fraud is not exclusive to North Koreans - approach it as such.**
3. Below is a list of 'red flags' that can help you evaluate with higher confidence if you are dealing with a DPRK IT
   Worker. However, always keep the above point in mind! For every 'obvious' DPRK IT Worker, there will be some who are
   able to evade most, if not all, of the following flags:
     1. **Is their video on?** If not, insist they enable their camera.
         1. Some DPRK IT Workers have no problem presenting as themselves (without a facilitator, AI, or disabled
            video). See if you recognize anyone from this
            [Collection of DPRK IT Workers photos](https://x.com/browsercookies/media).
     2. **Is the background visible or obscured?** An obscured background isn't always a red flag, but it can be
        helpful for the final assessment.
         1. DPRK IT Workers love "stock" backgrounds. You'll often find them using the Golden Gate Bridge as a
            backdrop. Other times, you may notice them sitting in low-quality housing where the workspace is only divided
            by temporary walls or rugs.
     3. Read:
        [Detect if it's an AI-generated face or
        deepfake](https://unit42.paloaltonetworks.com/north-korean-synthetic-identity-creation/).
     4. **Start with small talk** relevant to their claimed nationality and location. This is especially important if
        you're dealing with someone presenting as an Asian man but providing, for example, Latin American documents/names
        while claiming to live in Southeast Asia (an identity mismatch). **Note: While a smaller number of female DPRK IT
        workers have been identified, they do exist. In other cases, you might encounter hired female facilitators. If the
        candidate claims to be in your country, offer an on-site interview. Beware, DPRK IT workers may send a stand-in.
        Verify that the person attending is the same one from the call.**
     5. **Keep an open mind** about gender, nationality, and experience. **DPRK IT workers are known to use
        facilitators from all over the world. This means you might encounter a non-Korean individual on the call who is,
        in fact, a DPRK IT worker.** Similarly, a DPRK IT worker's portfolio can sometimes be impressive and not far off
        from their claimed experience. In previous instances, we've found profiles showing 2-3 years of work for reputable
        organizations.
     6. **Go through the candidate's background.** Verify the timelines of their claimed experience (e.g., "You worked
        at Company X from when to when?"). While the candidate answers, observe if they seem to be reading from a script.
        Try to mix up details from their claimed experience and note their reaction (e.g., "I see you worked at XYZ," when
        you know from their CV that they didn't). This is good general advice. If the candidate appears to be relying on
        ChatGPT for answers (reading from the screen), it's a red flag.
     7. **Conduct a language comprehension test.** If the candidate claims to be Japanese, ask them questions in
        Japanese. Beware, some DPRK IT workers can speak Japanese or Chinese, though their proficiency is often similar
        to their English skills (A1/A2 level). See: [North Korean failing to answer questions in Japanese despite claiming
        to be
        Japanese](https://www.ketman.org/dprk-it-workers-in-freelance-platform-onlyDust.html#:~:text=With%20the%20sole,can%20watch%20below.)
     8. **Ask if the candidate is at home or a co-working space.**
         1. Look for movement in the background.
         2. If they claim to be at home, you can try a quick KYC check: **ask them to show their ID card next to
            their face.**
     9. **Carefully observe the candidate's screen presentation if they share their screen.** Often, you might notice
        different GitHub, Gmail, or other social network profiles active on their screen than those claimed in their CV.
        It's best not to give the candidate a chance to prepare for this. Casually ask, "Could you walk us through your
        best code on GitHub by sharing your screen?"
     10. **Evaluating a potential DPRK IT Worker's GitHub profile:**
         1. The account creation date is later than the commits in its hosted repositories (an artificially aged
            account). This is especially suspicious if many repositories follow this pattern and the user claims experience
            aligning with the age of these manipulated commits. This can be a false positive but is usually easy to clear
            up. Some users re-upload their old code, pre-dating the GitHub account creation date. A false positive for this
            particular flag can be deduced from the overall quality of the account.
         2. A high number of followers and accounts followed (e.g., over 200). If the user is a popular developer
            with a significant online presence, this isn't a red flag. **False positives can occur for accounts that
            automatically follow back or for Developer Relations (DevRel) and recruitment professionals.**
         3. A high number of contributors to the user's repositories. If the user is not a popular developer, this
            is a red flag. Regular developers typically won't have 100+ contributors to their repositories without a
            significant online presence. **This flag has a tendency to be polluted with high numbers of contributors on
            "copied" repositories, where a DPRK IT Worker has "injected" themselves as an author but has also kept the
            original contributors' usernames.**
         4. Quality of opened Pull Requests and Issues. **It's useful to retrieve the full history of Pull Requests
            and Issues opened by the user and review them for quality.** For advanced DPRK IT workers, these may not differ
            significantly from those of regular developers. Additionally, if a suspicious user was `@pinged` in a PR or
            Issue, it might help uncover a previous nickname. Look for automated or spam-like text/code. DPRK IT Workers
            will often go for "quantity" over "quality." **At the same time, some DPRK IT Workers will be authors of
            perfectly valid Pull Requests and Issues - an artifact of their previous employment or a better
            credibility-building effort.**
         5. **Overly informative (full of images and stats) GitHub profile README/About page.**
             1. This can be a false positive. Regular developers have been observed to overuse this section.
         6. **Avatars.**
             1. DPRK IT workers often use AI-generated images (not necessarily faces) as their avatars.
                They typically use freely accessible models like Stable Diffusion or Midjourney.
             2. "Cartoonish" avatars are also popular: CGI-style images of fictional characters, Minion avatars,
                and NFT-related avatars (especially Pengu and Doodles).
             3. **Having no avatar at all is also common.**
             4. Reference:
                [Identifying Suspicious Github Accounts](https://www.ketman.org/identifying-suspicious-gh-accounts.html)
         7. **Social media links.**
             1. In many cases, there will be a Twitter link. It's always worth visiting.
                 1. Check the "Media" page for images uploaded by the account owner. **Can you find any
                    pictures from conferences or showing their physical appearance?** DPRK IT workers usually will not
                    post pictures from physical locations. **The exception to this rule would be "facilitator" or
                    "purchased/stolen" accounts.**
                 2. Look for job-begging tweets.
                 3. References:
                     1. [Nick Franklin Case - A well developed IT Worker
                        persona](https://x.com/tanuki42_/status/1905003045433290940)
                     2. [Nick Franklin Case - Activity across different
                        platforms](https://x.com/danielvf/status/1905642180749775189)
         8. **Suspicious interactions.**
             1. Contributions to low-quality external repositories and/or organizations. **DPRK IT workers are
                known to set up "fake" organizations on GitHub, often populated by other IT workers. Similarly, DPRK IT
                workers will cross-commit to each other's repositories.** It's worth checking the profiles of contributors
                to the potential threat actor's repositories: are these contributors legitimate themselves? A full data
                dump of the GitHub account may be useful, but cherry-picking a few repositories from the profile is often
                effective enough for a first pass.
                 1. Reference:
                    [A counter example - Good looking IT Worker Github
                    Profiles](https://x.com/blackbigswan/status/1873364567285449160)
         9. **Repositories.**
             1. "Copied repositories." DPRK IT workers will try to boost their credibility by pushing a clone
                of a legitimate repository to their own account (Google: "How to fake Github history"). They will often
                edit the `.git` config and insert their own account data. Usually, they won't remove all original
                contributors but will insert themselves among them. **Use GitHub's search feature to find the original
                repository by name, commit SHA, or a unique string extracted from within the repository. Compare the actual
                account creation date with the profile's UI-displayed history: is it consistent, or is the account's
                creation date more recent than the years of activity displayed?** A simple API query to get the account
                creation date from GitHub may be necessary here.
             2. GitHub's Activity Badge for contributing to an organization. Verify if it's an actual
                contribution like a PR or commit or just a spam Issue/Comment/PR. This is an often-utilized method for
                highly popular repositories (e.g., OpenZeppelin, Paradigm) where core developers are reluctant to merge
                spam PRs.
                 1. Reference: [DPRK IT Workers faking Github Activity
                Badges](https://x.com/blackbigswan/status/1876953373187920054/photo/1)
     11. **Evaluating other immediately available data points:**
         1. **Full Name.**
             1. Even if a full name is "fake," it can still be a useful data point. DPRK IT workers rotate their
                identities, but they need to maintain them for at least some time. **Another challenge they face is
                managing multiple personas; you may catch an "identity confusion" where a DPRK IT worker uses different
                names in different places, for example, a different name used/mentioned on GitHub than on a call or on
                other social profiles.** It's also possible to notice different names used with the same (or different)
                GitHub owner's email addresses.
                 1. Take extra care with Asian names, especially Chinese names. Chinese citizens often
                    westernize or shorten their full names in various ways. This doesn't necessarily mean they are
                    malicious.
             2. In most cases, DPRK IT workers prefer to use Asian (Japanese, Chinese, Korean) names. However,
                they are also known to use fake names from all around the world, corresponding to where their
                "facilitators" are based. This includes American names ("James" being an extremely popular choice) and
                even European names (e.g., Polish, Ukrainian, Hungarian).
                 1. DPRK IT workers may have access to KYC documents issued for their claimed nationality.
                    **You should be alarmed by highly unorthodox combinations**, such as an Asian man living in Indonesia
                    with Argentinian KYC documents.
         2. **Location.**
             1. Japan and the USA are extremely popular choices for claimed locations. Additionally, Southeast
                Asian countries like Thailand, Malaysia, Singapore, or Taiwan are also common. The actual physical location
                is commonly the DPRK (Pyongyang, border regions), China (border regions), Eastern Russia (Vladivostok),
                Laos (Vientiane), Indonesia, Vietnam, and parts of Africa. It's possible to obtain the IP address of a
                potential DPRK IT worker through a DocuSign document that collects HTTP headers. DPRK IT workers are known
                to utilize "laptop farms," meaning they can hide their IP behind an actual fixed/landline IP address in
                their claimed country of residence.
         3. **OSINT analysis.**
             1. We recommend checking each suspicious email address with a service like
                [https://epieos.com](https://epieos.com). It can provide additional data points, such as a LinkedIn
                profile, which can uncover further identity mismatches.
                 1. On LinkedIn, examine the strength of the actor's connection network.

## Did I hire a DPRK IT Worker?

1. The list below serves as a guide for confirming your suspicions if one of your employees is a potential
    DPRK IT Worker. We're focusing on using non-enterprise flags accessible to even the smallest of projects.
    The assumption is that your project has limited EDR/SIEM logging infrastructure (you should, however, consider
    implementing some monitoring infrastructure in the future).
     1. If your organization has EDR/SIEM capability, Read:
        [DTEX advisory on DPRK Insider Threat Kill
        Chain](https://www.dtexsystems.com/resources/i3-threat-advisory-inside-the-dprk/)
     2. Consider using GitHub Enterprise for your organization to have access to more detailed logs.
2. Before discussing the heuristics: **Don't focus on negating your suspicion; focus on clearing it up.
    It doesn't matter if you're checking a long-time employee who provides good technical output, is not Korean/Asian,
    logs into the workspace using a US-based IP, or came recommended. DPRK IT Workers have been known to successfully
    evade detection for YEARS.** Focus on creating a full profile of your employee and judge it based on the complete
    picture and any inconsistencies you find.
3. Below is a list of 'red flags' that should prompt immediate action from your side (e.g. a deep background check):
     1. **Avoiding real-life meetings.** Even if they initially agree to meet, they might come up with explanations
        as to why they can't. They often cite 'family reasons' or 'travel abroad.' The situation can repeat itself for
        every single meeting proposal, regardless of the location. **You can propose to meet at their location as a final
        test.**
     2. **Inconsistencies in work and communication.** It's often the case that a single DPRK IT Worker account is
        operated by a few individuals, especially if your company communication is sparse. One week you may observe good
        quality and high output; the next week, a significant drop. Similarly, for communication, you may observe the
        worker being overly 'mute' on all company sync calls or clueless as to what was discussed in previous meetings.
        They will also often have issues communicating about their code but not with the code development itself
        (a sign of more than one worker on a single account).
     3. **Timezone.** If your worker claims to be in Texas (GMT-5) but is located in Pyongyang (GMT+9), you may
        observe work patterns closer to North Korean time than to Texan time. Note that DPRK IT Workers work around the
        clock and can circumvent this flag easily.
     4. **Bogus work history.** Verify if the job history claimed on their CV is real. You can always reach out to
        the previous company for background information. In most cases, the history will be made up, but there are
        exceptions. DPRK IT Workers may list legitimate companies for which they did previous work but were let go
        (without that company's knowledge of their true nature). Sometimes, DPRK IT Workers will list organizations
        they control, so exercise caution when contacting anyone for background information.
     5. **Identity switch.** Be on guard if an employee's profile suddenly changes its nickname/identity.
        DPRK IT Workers do this often, usually when discovered in one of their previous jobs and for fear that someone
        will notify your company. **They may suddenly start using a different GitHub handle (this includes suddenly pushing
        a Pull Request using a different account than usual), delete their social media accounts, or get banned from
        LinkedIn.** Additionally, they may occasionally 'confuse' their fake identities and log in to your company
        workspace or a meeting using a completely different account.
     6. **Identity mismatch.** It should raise questions if your employee is Asian but provides non-Asian KYC
        documentation along with poor language skills. **Run a background check on all the data.** Can you find a person
        with the same name whose identity was potentially stolen or borrowed? Is the address provided legitimate, or does
        it seem 'random' (e.g., an empty house, a business venue)? Google "(Full Name of your worker) + sentenced" to see
        if the DPRK IT Worker bought a criminal's identity (an often-seen case with claimed US-based personas). Perform a
        reverse image search on your worker's profile pictures/avatars. Are there more similar accounts using the exact
        same image? **Beware that DPRK IT Workers have no issues providing credible-looking KYC documentation; some of
        these documents even pass authentication checks on specialized services.**
     7. **Recommending other suspicious accounts for work.** DPRK IT Workers will leverage their initial foothold
        in your organization to propose other DPRK IT Workers for a job. Their recommendations will usually follow the
        same patterns. Many organizations fall for it and hire multiple workers **(sometimes, as much as 50-70% of the
        entire company is composed of DPRK IT Workers if such tactics succeed).** Additionally, check if the potential
        DPRK IT Worker hasn't already added some of their 'friends' to your organization without your knowledge.
     8. **Proximity to other suspicious/spam accounts.** Don't be fooled by GitHub or Twitter accounts that are over
        10 years old. DPRK IT Workers can easily source these. However, check if your worker has any meaningful history of
        interaction with their followers/following. Or, do all accounts in proximity to your worker appear spam-like or
        like bots?
     9. **Poor social skills.** It's usually (but not always) the case that a DPRK IT Worker will have trouble with
        'small talk.' This isn't necessarily because of cultural differences (DPRK IT Workers are educated on Western
        culture and language as part of their job). It's often because of the sheer volume of remote gigs they handle
        and how confusing it can be. A DPRK IT Worker will prefer to always steer the conversation toward technical details.
     10.**Review Workspace logs (IP addresses).** Check if the IP addresses used to log in to your infrastructure
        are coming from the same location as claimed by the worker. VPNs, proxies, or Russian ISPs are red flags, as
        are highly inconsistent IP ranges (a mix of the sources mentioned). Beware that DPRK IT Workers are known to
        utilize "Laptop Farms."
        Read: [North Korea Infiltrates U.S. Remote Jobs - With the Help of Everyday Americans](https://archive.ph/Mb68C)
     11.**Payments.** North Koreans can organize a 'drop' bank account to receive wire transfers; however, their
        preferred method of receiving a salary will be through cryptocurrency, usually at a flat rate that they
        will not try to negotiate. In most cases, DPRK IT Workers will work at a discount to industry standards
        without complaining (25-50% discount). It may be the case that the worker's CEX account gets frozen, and they will
        come back to your organization for help unfreezing it (by providing proof of employment).

## After a DPRK IT Worker is hired by your company:

1. **The main goal of a DPRK IT Worker is to keep their job and salary coming for as long as possible.** It's worth
    understanding that DPRK IT Workers themselves vary in quality. For more 'senior' workers, keeping the job will be easy
    as their output and technical skills are high. For 'junior' ones, the engagement may end on the basis of poor
    performance.
     1. We have observed cases where DPRK IT Workers are fine with taking a salary cut to help a project stay afloat,
        as long as they continue to be paid.
2. **The highest risk to your organization, which occurs immediately after you on-board the DPRK IT Worker, is a data
    and secrets leak.** DPRK IT Workers do not care about your organization's and their operational security. When you
    assign access to a single DPRK IT Worker, you can be sure more individuals are using the same access. Unbeknownst to
    you, everything that's private to this single worker is now accessible over a (usually) poorly secured internal DPRK
    IT Worker network.
3. **We have observed DPRK IT Workers passing access or sensitive information to DPRK Hacking teams.**
    This is not often the case, as the goal of the DPRK IT Worker is to keep their job and salary as opposed to a one-time
    hack. However, if the target is high-value, they won't hesitate or may not even have a say in whether or not their
    employer is targeted for a hack.
4. Some DPRK IT Workers also perform tasks adjacent to malicious campaigns like the "Contagious Interview." Read:
    [North Korean Threat Actors lure tech job seekers as fake
    recruiters](https://unit42.paloaltonetworks.com/north-korean-threat-actors-lure-tech-job-seekers-as-fake-recruiters/)
    and [Two Campaigns by North Korea Bad Actors target job
    hunters](https://unit42.paloaltonetworks.com/two-campaigns-by-north-korea-bad-actors-target-job-hunters/).
    Your North Korean employee **may leverage the credibility granted by being employed at your company to conduct
    malware-related campaigns in the present and future.** This could significantly affect your brand.
5. **A DPRK IT Worker will try to escalate their access if possible**, whether by adding new members (who will also
    be getting paid) or by getting permissions to release builds and packages. Additionally, **we have encountered
    situations where DPRK IT Workers were added as signers to the multisig wallets** of the entire project as part
    of the dev team!
6. **DPRK IT Workers won't report code vulnerabilities to you** and may leave them for future exploitation.
    First, they generally do not care about and are not invested in the success of your project to protect it from
    being hacked. Second, they may intentionally leave the backdoor with the intent to use it in the future. Lastly,
    they may simply miss the vulnerability because they are overworked across numerous remote gigs they're performing
    at once.

In the next section [**Mitigating DPRK IT Workers**](/dprk-it-workers/mitigating-dprk-it-workers) we will be discussing
ways to harden your organization and employees against the DPRK IT Worker threat.

---


# Self-Adoption Guide

This guide walks you through the full process of self-adopting the SEAL Safe Harbor Agreement for your protocol. The
goal is to provide whitehats with legal clarity and confidence to rescue funds when it matters most.

To do this effectively, protocols should cover all public and legal bases: defining a clear scope, obtaining DAO
approval (if applicable), registering on-chain, updating their terms of service, and making a public announcement.

## 1. Scope Definition

The first step is defining the **scope**. This information informs whitehats about how and when they can intervene. It
includes which assets are covered, where to send rescued funds, how to contact your team, what bounties apply, and any
identity requirements.

- Refer to the scope walkthrough: [Scope Definitions & Tips](/safe-harbor/scope-terms)
- DAO Template:
[DAO Scope Template](https://docs.google.com/document/d/1zsyutbSpQrwkmEA_XicABoRkSR25IQr92tOPgZOixN4/edit)
- Non-DAO Template:
[Non-DAO Scope Template](https://docs.google.com/document/d/1kcgeq2GmmuSHyMzbl0mlgRhMHag-av4B4TdLZFqdoSE/edit)

## 2. DAO Proposal (If applicable)

If you are a DAO, this is a critical step. It formalizes permission from the community and provides legitimacy to the
adoption.

- DAOs do **not** need a legal entity. Safe Harbor was designed to allow on-chain communities to adopt the agreement
natively.
- Use the DAO Proposal draft from Step 1 where you defined the scope. Feel free to edit the proposal to reflect your
DAO’s tone and format.
- Push your proposal through governance, temp check → formal proposal → Snapshot/Tally/etc.
- (Optional) Include the **on-chain adoption call** in the proposal itself for a full end-to-end flow.

## 3. On-Chain Adoption

Whether you're a DAO or a centralized team, you'll need to publish your adoption on-chain. This ensures your terms are
publicly visible and enforceable.

**If you are NOT doing on-chain via DAO proposal:**

- Follow the guide: [SEAL Safe Harbor On-Chain Adoption](/safe-harbor/on-chain-adoption-guide)

**If you ARE doing this in your DAO proposal:**

- On-chain adoption involves two parts:
    1. Creating the AgreementV2 contract (the "terms" container)
    2. Registering it in the Safe Harbor Registry (this is what matters for whitehats)
- The DAO proposal should handle **step 2**, while step 1 can be done beforehand by following the guide:
[SEAL Safe Harbor On-Chain Adoption](/safe-harbor/on-chain-adoption-guide)
(**IMPORTANT**: Be sure to set the `owner` of the agreement to your DAO address)

## 4. Update Terms of Service & Docs

To ensure all users are informed and legally covered, update your Terms of Service and documentation.

### Terms of Service (TOS)

Add the following language to your TOS:

> User Agreement to be Bound By Agreement, Consent to Attempted Eligible Funds Rescues and Payment of Bounties
>
>
> The User hereby acknowledges and agrees to, and consents to be bound by the terms and conditions of, that certain Safe
> Harbor Agreement for Whitehats, adopted by the Protocol Community on [INSERT DATE HERE] (the ”Whitehat Agreement”),
> available here
> [https://bafybeigvd7z4iemq7vrdcczgyu2afm7egxwrggftiplydc3vdrdmgccwvu.ipfs.w3s.link](https://bafybeigvd7z4iemq7vrdcczgyu2afm7egxwrggftiplydc3vdrdmgccwvu.ipfs.w3s.link/),
> as a "User" and member of the "Protocol Community" thereunder. Without limiting the generality of the foregoing:
>
> - the User hereby consents to Whitehats attempting Eligible Funds Rescues of any and all Tokens deposited into the
> Protocol by the User and the deduction of Bounties out of User’s deposited Tokens to compensate Eligible Whitehats for
> successful Eligible Funds Rescues;
> - the User acknowledges and agrees that Tokens may be lost, stolen, suffer diminished value, or become disabled or
> frozen in connection with attempts at Eligible Funds Rescues, and assumes all the risk of the foregoing;
> - the User acknowledges and agrees that payment of the Bounty as a deduction from User’s Tokens to an Eligible
> Whitehat may constitute a taxable disposition by the User of the deducted Tokens, and agrees to assume to all risk of
> such adverse tax treatment; and
> - the User agrees to hold the other Protocol Community Members harmless from any loss, liability or other damages
> suffered by the User in connection with attempted Eligible Funds Exploits under the Whitehat Agreement.

This is also found in Exhibit D in the legal agreement

### Documentation

Under your documentation's "Security" or "Bug Bounty" section, include:

> "This protocol has adopted the SEAL Safe Harbor Agreement for Whitehats, which empowers approved security researchers
> to intervene during active exploits to rescue funds. Full adoption details, scope, and bounty terms are publicly
> available [here]."

Replace `[here]` with your actual registry listing or agreement address.

## 5. Announcement

Once everything is live, it's time to communicate publicly. This signals to whitehats, users, and the broader ecosystem
that your protocol is protected.

- Use Twitter, Discord, forums, and governance portals.
- Highlight your on-chain registration, bounty terms, and any DAO vote.
- Example announcement:

    > Today, we’re proud to announce that [Protocol Name] has officially adopted the @_seal_org Safe Harbor Agreement -
a legal and technical framework that empowers whitehats to rescue funds during active exploits.
    >
    >
    > This move brings us into alignment with some of the most security-forward protocols in the space - Uniswap,
    Pendle, Balancer - as we take real steps to defend our community and user funds.
    >
- Feel free to coordinate with SEAL - we're happy to co-announce and amplify it.

---

If your protocol ever needs help with adoption, SEAL is happy to help answer any questions, walk you through adoption,
amplify announcements, etc

📬 Contact us at: [safe-harbor@securityalliance.org](mailto:safe-harbor@securityalliance.org)

---


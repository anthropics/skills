# Safe Harbor for Whitehats

## Why You Should Care

{/* TODO: link not found (./key-terms.md#active-exploit)*/}
Safe Harbor lets whitehats intervene during [active exploits] to help secure protocol funds. It does so by providing a
legal framework that outlines what whitehats can and can't do, how they ought to operate, and protects abiding
whitehats in the event of legal action taken by the protocol.

In addition to the legal protections, Safe Harbor also helps whitehats by giving them the following information:

1. What assets are owned by a protocol
{/*TODO: link not found (./key-terms.md#asset-recovery-address)*/}
2. What is the protocol's ([asset recovery address])
{/* TODO: (../security-contact.md) is this link this: /vulnerability-disclosure/security-contact ? */}
3. Who the [security contact]
4. What KYC requirements (if any) protocols impose onto whitehats
5. What bounty terms whitehats will be awarded under Safe Harbor

This information is all neatly cataloged in the [Safe Harbor Registry]
{/*TODO: link not found (./key-terms.md#safe-harbor-registry)*/} - an on-chain registry cataloging all protocol
adoptions and their adoption details. For more details, review the [Safe Harbor for Protocols]
{/*TODO: link not found (./protocol.md)*/} document.
It has also been compiled by Skylock at the [Safe Harbor Database](skylock.xyz/safeharbor/database).

## Whitehat Adoption

If a whitehat reads and understands the entire legal framework, they may later be eligible to participate in a whitehat
rescue. These rescues should only be taken in very specific circumstances, and it is important to reiterate the
following:

- The framework only applies to active exploits, and it is a violation of the agreement if the whitehat initiates an
exploit themselves.
- The protocol is not responsible for ensuring the whitehat follows the law, and the whitehat can not be protected from
criminal charges outside the agreement's scope.
- There are nuances that can affect the agreement's enforceability, and whitehats will assume many legal risks by
becoming involved.
- If the whitehat decides to proceed with a whitehat rescue, they must follow the process specified in the agreement.
This includes transferring rescued funds to the protocol's "Asset Recovery Address" and promptly notifying the protocol
of the fund recovery. The whitehat may keep (or later receive) a reward, based on the terms of the agreement.

Safe Harbor may also apply to generalized frontrunner / arbitrage bots. The rules of conduct enforced by Safe Harbor for
[Prospective and Retrospective] {/*TODO: link not found (./key-terms.md#prospective--retrospective-whitehats)*/}
whitehats differs in a few key areas.

## In the Event of a Hack

### Pre-Intervention

In the event of a hack targeting a protocol that has adopted Safe Harbor, whitehats are permitted to take broad actions
to secure the protocol's funds. Before taking action, review the following checklist (also present in the Safe Harbor
Technical Summary):

- Is this an active, urgent exploit?
- Are you unable to responsibly disclose the exploit (e.g. via a bug bounty program) due to time constraints or other
reasons?
- Can you reasonably expect your intervention to be net beneficial, reducing total losses to the protocol and associated
 entities?
- Are you experienced and confident in your ability to manage execution risk, avoiding unintentional loss of funds?
- Will you avoid intentionally profiting from the exploit in any way other than through the reward granted by the
protocol?
- Are you and anyone with whom you directly cooperate during the funds rescue, as well as all funds and addresses used
in said rescue, free from OFAC sanctions and/or other connections to sanctioned parties?
- Have you confirmed the agreement has been duly adopted by the protocol community?
- Are you fully aware of the risks associated with your actions, including but not limited to accidental loss of funds,
claims and liabilities outside this agreement's scope, and the unclear extent of this agreement's enforceability?

In the event that all the above applies, you may chose to take action to protect the protocol's assets. How you do this
depends on the situation - perhaps offensively white-hat hacking a protocol with a proven exploit, or returning funds
recovered by your MEV bot from an incident it frontran.

### Post-Intervention

After the funds have been recovered, it is your responsibility to ensure their safe return to the owner protocol. We
strongly recommend contacting [SEAL911](incident-management/seal-911-war-room-guidelines) immediately to advise on the
fund recovery process and to assist with KYC, protocol communications, and bounty collection. You must also contact the
protocol's posted security contact and return all recovered funds to the protocol's [asset recovery address]
{/*TODO: link not found (./key-terms.md#asset-recovery-address)*/} within 6 hours of the event, or 48 hours if
reason is provided and the protocol has been made aware.

---


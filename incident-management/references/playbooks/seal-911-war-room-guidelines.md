# SEAL 911

SEAL 911 is a project designed to give users, developers, and even other security researchers an accessible method to
contact a small group of highly trusted security researchers. The group can be reached via the [Telegram
bot](https://t.me/seal_911_bot).

Members of SEAL 911 follow a strict
[CODE OF CONDUCT](https://github.com/security-alliance/seal-911/blob/main/CODE_OF_CONDUCT.md).

When interacting with SEAL 911, ensure that you give as much information as possible in order to avoid double work by
the security researchers.

## Crisis Handbook - Smart Contract Hack | [Google Doc](https://docs.google.com/document/d/1DaAiuGFkMEMMiIuvqhePL5aDFGHJ9Ya6D04rdaldqC0/edit#heading=h.c4h2beeflqpo)

### Actions Checklist

### Perform Immediately

- [ ] Notify SEAL 911 Bot of the incident. Use this message template to get started.
- [ ] Create a War Room with audio and share the invite link with trusted individuals.
- [ ] Duplicate this document to allow collaboration and share the link in the War Room.
- [ ] Review the Advice to Keep in Mind section.

### Perform in Parallel by Role

1. **Assign Key Roles to War Room Members**:
   - [ ] Assign members to specific roles.

2. **Analysis**:
   - [ ] Scope the impact of the attack.
   - [ ] Gather Transactions Involved.
   - [ ] Gather Affected Addresses.
   - [ ] Record Funds Movement.
   - [ ] Gather Attacker Information.
   - [ ] Investigate the issue and update the Issue Description.
   - [ ] Propose workable solutions.

3. **Protocol actions**:
   - [ ] Take immediate corrective/preventative actions to prevent further loss of funds.
   - [ ] Pause contracts if possible.
   - [ ] Execute pre-made defensive scripts.
   - [ ] Prioritize proposed solutions.
   - [ ] Validate and execute the solution.
   - [ ] Prepare monitoring alerts for situations that require future actions.

4. **Web actions**:
   - [ ] Disable deposits and/or withdrawals as needed in the web UI.
   - [ ] Enable front-end IP or Address blacklisting.
   - [ ] Create front-end for any user actions necessary (approval revoking, fund migrating, etc.).

5. **Communications**:
   - [ ] Identify social platforms that communications on the incident must be sent to.
   - [ ] Prepare messages for incident communication internally and externally.
   - [ ] Gather security contacts for any potentially affected downstream protocols (bridges, lending protocols).
   - [ ] Notify block explorers (like Etherscan) for attacker address labeling.
   - [ ] Continuously monitor social media for users providing additional information that aids whitehat efforts.
   - [ ] Monitor War Room efforts and maintain the Event Timeline.

### After all of the above is complete, consider Post Incident Actions

## Information Gathering

Information will primarily be shared and acted upon in the War Room. As time allows, consolidate intel in the below
section to achieve the following:

- Accurately scope the incident impact.
- Inform new War Room members and third parties efficiently.
- Aid external communication.

This is the chief duty of the Scribe.

### Issue Description

The issue involves an unauthorized transfer of funds from the protocol's treasury contract due to a vulnerability in the
contract's access control mechanism. The attacker exploited this vulnerability to initiate multiple transfers,
siphoning funds to an external wallet.

### Events Timeline

Record events to construct an overall timeline of the incident. Events worth recording:

- First notice of the incident
- War room creation
- External communications
- Attack transactions
- Transactions performed by the team

Record times in UTC. Use a UTC Time Converter.

| Date-Time (UTC)   | Event Description                   | Notes                            |
| ----------------- | ----------------------------------- | -------------------------------- |
| 2024-08-23 12:45  | First notice of the unauthorized transfer | Alert received via monitoring system |
| 2024-08-23 12:50  | War room created                    | Initial members invited          |
| 2024-08-23 13:05  | Notified SEAL 911 Bot               | Incident report submitted        |
| 2024-08-23 13:15  | Attack transaction identified       | Transaction hash: 0x123456789abc |
| 2024-08-23 13:20  | Contracts paused                    | Prevented further fund transfers |
| 2024-08-23 13:30  | External communication initiated    | First update sent via Twitter    |

### Transactions Involved

Record all transactions related to the incident.

| Transaction Link                                                      | Notes                                |
| --------------------------------------------------------------------- | ------------------------------------ |
| [0x123456789abcdef...](https://etherscan.io/tx/0x123456789abcdef)     | Initial exploit transaction          |
| [0xabcdef123456789...](https://etherscan.io/tx/0xabcdef123456789)     | Attacker moving funds to mixer       |
| [0xfedcba987654321...](https://etherscan.io/tx/0xfedcba987654321)     | Defensive move by the team           |

### Affected Addresses

Record affected addresses related to the incident (protocol contracts, bridges, users, etc.).

| Address Link                                                    | Status      | Notes                               |
| --------------------------------------------------------------- | ----------- | ----------------------------------- |
| [0x1111222233334444...](https://etherscan.io/address/0x11112222) | At Risk     | User wallet, interacted with exploit |
| [0x5555666677778888...](https://etherscan.io/address/0x55556666) | Impacted    | Protocol treasury address            |
| [0x99990000aaaabbbb...](https://etherscan.io/address/0x99990000) | Paused      | Lending protocol contract            |
| [0xaaaabbbbccccdddd...](https://etherscan.io/address/0xaaaabbbb) | Saved       | Bridge contract, funds secured       |
| [0xddddeeeeffff0000...](https://etherscan.io/address/0xddddeeee) | Needs Review| User wallet, unusual activity noted  |
| [0x2222333344445555...](https://etherscan.io/address/0x22223333) | Uncertain   | User wallet, pending analysis        |

### Funds Movement

Record funds movement to gather the impact of the incident and organize recovery efforts.

- Original address that held the funds
- Transaction that moved the funds
- Assets and amounts the funds are comprised of
- Destination the funds moved to (Contract, CEX, Bridge, Mixer)
- Recovery Status of the funds

Use Phalcon Tx Explorer to aid in recording funds movement.

| Origin                                                      | Transaction Link                                             | Amount / Asset | Destination                                        | Recovery Status | Notes                               |
| ----------------------------------------------------------- | ------------------------------------------------------------ | -------------- | ------------------------------------------------- | --------------- | ----------------------------------- |
| [0x5555666677778888...](https://etherscan.io/address/0x5555) | [0xabcdef123456789...](https://etherscan.io/tx/0xabcdef)     | 1000 ETH       | [Mixer address](https://etherscan.io/address/0x12)| Needs Review    | Funds moved to Tornado Cash        |
| [0x99990000aaaabbbb...](https://etherscan.io/address/0x9999) | [0x9876543210fedcba...](https://etherscan.io/tx/0x987654)    | 500,000 DAI    | [CEX address](https://etherscan.io/address/0x34)  | In Progress     | Funds transferred to centralized exchange |
| [0xaaaabbbbccccdddd...](https://etherscan.io/address/0xaaaa) | [0x123456789abcdef...](https://etherscan.io/tx/0x123456)     | 200 BTC        | [Contract address](https://etherscan.io/address/0x56) | Recovered       | Funds recovered via multisig       |
| [0xddddeeeeffff0000...](https://etherscan.io/address/0xdddd) | [0xfedcba987654321...](https://etherscan.io/tx/0xfedcba)     | 50,000 USDC    | [Bridge address](https://etherscan.io/address/0x78)| Uncertain       | Funds possibly moved cross-chain   |

### Attacker Information

Gather attacker information to aid legal efforts and fund recovery.

| Address Link                                                    | Funded By | Notes                                 |
| ---------------------------------------------------------------- | --------- | ------------------------------------- |
| [0xabcdefabcdefabcd...](https://etherscan.io/address/0xabcdefab) | Tornado Cash | Initial funding from Tornado Cash mixer |
| [0x123456789abcdef...](https://etherscan.io/address/0x12345678)  | CEX       | Received funds from centralized exchange |
| [0xfedcba987654321...](https://etherscan.io/address/0xfedcba98)  | Unknown   | No prior activity, potentially new wallet |

## Post Incident Actions

1. Confirm the incident has been resolved.
2. Create monitoring alerts for situations requiring future actions.
3. Prepare scripts to perform any actions related to monitoring events in the future.
4. Consider creating additional defensive scripts (pause/upgrade) to use for future situations.
5. Schedule a Post Mortem write-up.
6. Post the write-up to relevant social media.

## Appendix

### Advice to Keep in Mind

- Limit the War Room occupancy. Be careful not to invite too many people during the early stages. Sensitive information
is being shared; be wary.
- Make it clear to War Room members not to publicize information without the protocol’s consent.
- Do not speak to the press/news/publications.

### Key Roles

- **Operations**: Initiates War Room, assigns roles, distributes tasks, herds multisig participants.
  - *Person Responsible*
- **Scribe**: Consolidates gathered information for efficiency in knowledge-sharing.
  - *Person Responsible*
- **Strategy Lead**: Prioritizes actions, considers trade-offs of decisions.
  - *Person Responsible*
- **Protocol Lead**: Responsible for smart-contract actions (pausing, upgrading, etc.).
  - *Person Responsible*
- **Web/Infrastructure Lead**: Responsible for updating the front-end, managing servers.
  - *Person Responsible*
- **External Communicator**: Social media and user communications.
  - *Person Responsible*

### Suggested Tools and Platforms

| Name                  | Type            | Notes |
| --------------------- | --------------- | ----- |
| Discord               | Platform        | A familiar platform for web3 collaboration. Spin up a server quickly using our [recommended template](https://discord.new/CkADqy5aWsAH). Tips: New users must be granted the `approved` role before they can view chats. Upon creation, grant yourself the `approved` role and share an invite link with trusted members. |
| Telegram              | Platform        | A familiar platform for web3 collaboration. Tips: Upon New Group creation, enable chat history as visible to new members. To do this: Info -> Edit -> Chat History For New Members -> Visible |
| Google Hangouts       | Platform        | |
| Phalcon Tx Explorer   | Tx Analysis     | |
| Openchain Trace Explorer | Tx Analysis  | |
| Tenderly Tx Explorer  | Tx Analysis, Debugging | Some features require login. |
| Tenderly Alerts       | Monitoring      | Monitor addresses, on-chain actions, etc. Requires login. |
| MetaSleuth            | Monitoring      | Monitor fund movement. 50 address limit. Requires login (premium feature). |
| Github / Gist         | Code Sharing    | Create a private repo or secret gists and share the link with War Room participants only. |
| CodeShare             | Code Sharing    | Sessions expire after 24 hours. |
| HackMD                | Code Sharing    | Private notes become published after ~48 hours. Be very careful with sensitive information! |

### SEAL Message Template

Fill out with relevant information and send to SEAL 911 Bot.

```plaintext
Protocol: [Protocol Name]
Attack Tx(s): [Transaction Hash(es)]
Funds at Risk: [Estimated Amount in USD or Token]

[Brief Description of the incident]
```

---


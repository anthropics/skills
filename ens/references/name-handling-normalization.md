# Name Handling & Normalization

## Normalize Names per [ENSIP-15](https://docs.ens.domains/ensip/15)

- Always normalize ENS names before creating namehash, labelhash, or DNS-encoding
- Use established libraries that correctly implement ENSIP-15 normalization (like @adraffy/ens-normalize)
- Apply normalization at the earliest possible point in your ENS handling logic
- Include normalization checks in validation procedures for user-entered names

**Rationale**: ENS uses a specific normalization algorithm defined in ENSIP-15 to ensure consistent handling of Unicode
characters and emoji sequences. Failing to normalize names correctly can result in different hash values for what users
perceive as the same name, leading to resolution failures, security vulnerabilities, and poor user experience. Proper
normalization is fundamental to the correct operation of any ENS integration and must be performed before any
cryptographic operations (namehash, labelhash) or encoding. Using established libraries ensures compliance with the
complex requirements of ENSIP-15.

## Implement Security Measures for Homograph Attacks

- Detect and warn users about visually confusable characters in ENS names
- Display names using fonts that clearly differentiate similar-looking characters
- Consider displaying the script/language of characters in multi-script names
- Implement visual indicators for mixed-script names or potentially deceptive names
- When displaying ENS names, highlight or annotate unexpected character sets

**Rationale**: Homograph attacks use visually similar characters from different Unicode scripts to create deceptive
names (e.g., using Cyrillic 'о' instead of Latin 'o'). While ENSIP-15 addresses some confusables, it cannot eliminate
all visual ambiguities. Implementing additional security measures helps users identify potentially deceptive names
before interacting with them. These protections are particularly important in financial applications or any context
where users might send assets to an ENS name, as homograph attacks can lead to irreversible asset loss.

## Properly Handle Emoji in ENS Names

- Ensure your UI correctly displays emoji in ENS names at appropriate sizes
- Be aware that emoji rendering varies across platforms and fonts
- Handle emoji sequences correctly, including skin tone modifiers and ZWJ sequences
- Test thoroughly with emoji-containing names on multiple platforms and browsers
- Use libraries that correctly implement UTS-51 (Unicode Emoji) for handling emoji

**Rationale**: Emoji are increasingly common in ENS names but introduce technical challenges. Emoji can be composed of
multiple code points, including zero-width joiners (ZWJ) and variation selectors, making proper handling critical.
Incorrect emoji implementation can cause names to appear differently across platforms or fail to resolve correctly.
Emoji rendering also varies significantly between operating systems and browsers, requiring thorough cross-platform
testing to ensure consistent user experience.

---


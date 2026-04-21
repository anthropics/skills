# Smart Contract Integration

## Name Your Smart Contracts

- Register ENS names for core contracts in your project's ecosystem
- Set appropriate reverse records for your contracts
- Document contract ENS names in project documentation
- Consider naming contracts at deployment time to ensure immediate resolvability
- Use a standard pattern for contract naming to improve discoverability

**Rationale**: Smart contracts typically have complex hexadecimal addresses that are error-prone when shared or
referenced. By assigning ENS names to smart contracts, developers can significantly improve user experience, make
documentation more approachable, and reduce the risk of address errors. This practice is especially important for
contracts that interact directly with users or serve as key infrastructure components. Human-readable names also aid in
contract verification, as users can more easily confirm they're interacting with official protocol contracts rather than
potential phishing imitations.

## Leverage ENS as an Infrastructure Component

- Use ENS for service discovery between contract components
- Build upgradeability mechanisms that leverage ENS for implementation pointers
- Consider ENS as a registry for official protocol extensions and integrations
- Use ENS records to store protocol metadata in a human-readable format

**Rationale**: ENS can serve as more than just a human-readable address layer, it can function as critical
infrastructure for contract systems. Using ENS for implementation pointers enables flexible and upgradeable
architectures, as contract dependencies can be redirected without requiring contract redeployment. This pattern supports
robust governance models while maintaining a consistent user interface. Additionally, using ENS to register official
extensions creates a trust layer that helps users identify legitimate protocol integrations, while storing protocol
metadata in ENS records improves discoverability and system documentation.

---


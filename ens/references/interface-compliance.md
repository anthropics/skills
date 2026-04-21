# Interface Compliance

## Verify Resolver Interface Support

- Always check if a resolver supports your target interface using EIP-165
- Call supportsInterface() before attempting to use specific resolver methods
- Implement graceful fallbacks when interfaces aren't supported
- Cache interface support results to minimize redundant on-chain calls

**Rationale**: ENS resolvers can implement various interfaces, each providing different functionality (addresses, text
records, content hashes, etc.). Not all resolvers implement all interfaces, so checking interface support before calling
specific methods prevents failed transactions and improves reliability. This verification step is especially important
as the ENS ecosystem evolves and new resolver interfaces are introduced. Without proper interface verification,
applications may fail when encountering resolvers with limited functionality or custom implementations.

## Signal Supported Interfaces in Custom Resolvers

- When writing custom resolvers, properly implement EIP-165
- Signal all supported interfaces via supportsInterface()
- Document which interfaces your resolver supports
- Consider incremental implementation of interfaces based on user needs

**Rationale**: Implementing EIP-165 interface detection allows other contracts and applications to programmatically
discover what functionality your resolver supports. This promotes interoperability and ensures your custom resolver can
seamlessly integrate with the broader ENS ecosystem. Proper interface signaling is not just a technical requirement but
a key element of good blockchain protocol citizenship. Without it, other contracts and applications can't reliably
determine the capabilities your resolver offers, leading to poor user experiences and potential security risks.

## Stay Updated with ENS Improvement Proposals (ENSIPs)

- Regularly monitor the [ENS GitHub repository](https://github.com/ensdomains/ensips) for new ENSIPs
- Participate in ENSIP discussions to provide implementer feedback
- Implement support for new ENSIPs after they reach "Final" status
- Plan for deprecation of older interfaces as specified by [ENSIPs](https://docs.ens.domains/ensip/)
- Test implementations against the reference implementations provided in ENSIPs

**Rationale**: The ENS protocol evolves through the ENSIP process, which introduces new interfaces, standards, and
recommended practices. Staying current with these proposals ensures your implementation remains compatible with the
broader ecosystem and can leverage new functionality as it becomes available. ENSIPs often address security
vulnerabilities, improve user experience, or add valuable new features that users will come to expect. Implementers who
track and promptly adopt new ENSIPs gain competitive advantages while contributing to the overall health and advancement
of the ENS ecosystem.

---


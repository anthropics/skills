# Cross-Chain Compatibility

## Respect Cointype for [Chain-Specific Resolution](https://docs.ens.domains/ensip/9)

- Always use the correct cointype parameter when resolving addresses on specific chains
- For EVM-compatible chains, derive cointypes from chain IDs according to [ENSIP-11](https://docs.ens.domains/ensip/11)

**Rationale**: An ENS name can resolve to a different address for each different blockchain network, which ENS supports
through the cointype field in address records (following SLIP-44 standards). With the rise of smart contract wallets and
 account abstraction, users may have different addresses across different chains. Failing to respect the cointype when
resolving addresses can lead to funds being sent to addresses that don't exist on the target chain or that belong to
different entities altogether.

## Implement CCIP-Read Support

- Properly support and handle CCIP-Read functionality [EIP-3668](https://eips.ethereum.org/EIPS/eip-3668)
- Set reasonable timeouts and fallbacks for CCIP-Read operations

**Rationale**: CCIP-Read (EIP-3668) enables off-chain data retrieval for ENS resolution, allowing for more complex
resolution patterns and greater flexibility for name owners. This protocol allows resolvers to redirect resolution
requests to off-chain services that can implement custom logic beyond what's practical on-chain. Applications that
ignore CCIP-Read requests limit the functionality available to ENS users and may provide incorrect resolution results.
Supporting this standard ensures compatibility with advanced ENS use cases.

## Test Multi-Chain Implementations

- Test ENS resolution across all chains your application supports
- Implement proper error handling for unsupported chains
- Document which chains are supported by your implementation

**Rationale**: As blockchain ecosystems expand, users expect applications to work across multiple networks. Testing ENS
resolution across different chains ensures consistent behavior regardless of which network a user is connected to. Clear
 documentation about chain support also helps users understand the limitations of your application.

## Handle Reverse Records Per Chain

- Query reverse records on the chain where the address exists, not just mainnet
- Consider user context when displaying names, prioritize the reverse record from the chain the user is currently
  interacting with
- Validate reverse record ownership by checking if the returned name actually resolves back to the queried address on
  that chain

**Rationale**: With [ENSIP-19](https://docs.ens.domains/ensip/19), reverse records (address-to-name lookups) can now be
set and queried on any chain, not just Ethereum mainnet. This allows users to set different reverse records for the same
address across different networks, enabling more contextual and chain-specific identity resolution. Applications that
only check mainnet reverse records will miss valid reverse resolutions on other chains where users are actually active,
leading to incomplete or incorrect identity displays.

---


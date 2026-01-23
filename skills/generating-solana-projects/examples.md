# Examples

Complete examples of projects you can generate with this skill.

## Example 1: Simple Voting System

**User Request**: "Create a Solana voting system where users can create polls and vote"

**Generated Project**: `solana-voting-system`

### Project Structure
```
solana-voting-system/
├── programs/voting_system/
│   └── src/
│       ├── lib.rs
│       ├── state.rs (Poll, Vote accounts)
│       ├── errors.rs
│       └── instructions/
│           ├── initialize_poll.rs
│           ├── cast_vote.rs
│           └── close_poll.rs
├── tests/voting_system.ts
└── app/ (Next.js frontend)
```

### Key Features
- Create polls with multiple options
- Cast votes (one per user)
- Close polls and view results
- Real-time vote counting in UI

---

## Example 2: NFT Marketplace

**User Request**: "Build a Solana NFT marketplace with listing and offers"

**Generated Project**: `solana-nft-marketplace`

### Project Structure
```
solana-nft-marketplace/
├── programs/nft_marketplace/
│   └── src/
│       ├── lib.rs
│       ├── state.rs (Listing, Offer accounts)
│       ├── errors.rs
│       └── instructions/
│           ├── create_listing.rs
│           ├── make_offer.rs
│           ├── accept_offer.rs
│           └── cancel_listing.rs
├── tests/nft_marketplace.ts
└── app/
    └── src/
        └── components/
            ├── ListingCard.tsx
            ├── CreateListing.tsx
            └── OfferModal.tsx
```

### Key Features
- List NFTs for sale
- Make and accept offers
- Cancel listings
- Browse marketplace UI

---

## Example 3: Token Staking Platform

**User Request**: "Create a token staking platform with rewards"

**Generated Project**: `solana-token-staking`

### Project Structure
```
solana-token-staking/
├── programs/token_staking/
│   └── src/
│       ├── lib.rs
│       ├── state.rs (StakePool, UserStake accounts)
│       ├── errors.rs
│       └── instructions/
│           ├── initialize_pool.rs
│           ├── stake_tokens.rs
│           ├── unstake_tokens.rs
│           └── claim_rewards.rs
├── tests/token_staking.ts
└── app/ (Staking dashboard)
```

### Key Features
- Initialize staking pools
- Stake/unstake tokens
- Calculate time-based rewards
- Claim rewards
- Dashboard showing APY and stats

---

## Example 4: DAO Governance

**User Request**: "Build a DAO with proposal voting and treasury management"

**Generated Project**: `solana-dao-governance`

### Project Structure
```
solana-dao-governance/
├── programs/dao_governance/
│   └── src/
│       ├── lib.rs
│       ├── state.rs (Dao, Proposal, Member accounts)
│       ├── errors.rs
│       └── instructions/
│           ├── initialize_dao.rs
│           ├── add_member.rs
│           ├── create_proposal.rs
│           ├── vote_proposal.rs
│           └── execute_proposal.rs
├── tests/dao_governance.ts
└── app/ (Governance portal)
```

### Key Features
- Create DAO with members
- Submit proposals
- Vote on proposals with weights
- Execute approved proposals
- Treasury management

---

## Example 5: Escrow Service

**User Request**: "Create an escrow service for secure P2P transactions"

**Generated Project**: `solana-escrow`

### Project Structure
```
solana-escrow/
├── programs/escrow/
│   └── src/
│       ├── lib.rs
│       ├── state.rs (Escrow account)
│       ├── errors.rs
│       └── instructions/
│           ├── initialize_escrow.rs
│           ├── exchange.rs
│           └── cancel_escrow.rs
├── tests/escrow.ts
└── app/ (Escrow interface)
```

### Key Features
- Initialize escrow with tokens
- Exchange tokens between parties
- Cancel escrow and refund
- Secure atomic swaps

---

## Common Patterns Across Examples

### State Account Pattern
```rust
#[account]
pub struct ExampleState {
    pub authority: Pubkey,      // 32 bytes
    pub created_at: i64,        // 8 bytes
    pub is_active: bool,        // 1 byte
    pub bump: u8,               // 1 byte
}

impl ExampleState {
    pub const MAX_SIZE: usize = 8 + 32 + 8 + 1 + 1;
}
```

### Instruction Handler Pattern
```rust
pub fn handler(ctx: Context<InstructionName>, params: Params) -> Result<()> {
    // Validation
    require!(condition, ErrorCode::CustomError);

    // Business logic
    let account = &mut ctx.accounts.account;
    account.field = params.value;

    Ok(())
}
```

### Frontend Integration Pattern
```tsx
const handleTransaction = async () => {
    if (!wallet.publicKey || !program) return;

    try {
        const tx = await program.methods
            .instructionName(params)
            .accounts({
                account: accountPubkey,
                user: wallet.publicKey,
                systemProgram: SystemProgram.programId,
            })
            .rpc();

        console.log("Transaction:", tx);
    } catch (error) {
        console.error("Error:", error);
    }
};
```

---

## Deployment Example

After generating any project:

```bash
# 1. Install dependencies
yarn install
cd app && yarn install && cd ..

# 2. Generate and configure program ID
anchor keys list
# Copy the program ID and update in:
# - Anchor.toml
# - programs/{name}/src/lib.rs (declare_id!)
# - app/src/utils/anchorSetup.ts (PROGRAM_ID)

# 3. Build the program
anchor build

# 4. Start local validator
solana-test-validator

# 5. Deploy (in another terminal)
anchor deploy

# 6. Run tests
anchor test --skip-local-validator

# 7. Start frontend (in another terminal)
cd app && yarn dev
```

Visit `http://localhost:3000` to interact with your dApp.

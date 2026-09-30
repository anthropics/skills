# NFTs and AtomicAssets on XPR Network

This guide covers NFT development on XPR Network using the AtomicAssets standard - the primary NFT framework for EOSIO-based chains.

## AtomicAssets Overview

AtomicAssets is a RAM-efficient NFT standard developed by pink.network. Key benefits:

- **RAM efficient**: 151 bytes per asset, dApp pays RAM (not users)
- **No claim required**: Transfers are instant, no user action needed
- **Built-in trading**: Native two-sided trade offers
- **Notification hooks**: Assets can trigger smart contract logic
- **Token backing**: NFTs can be backed by fungible tokens

---

## Core Concepts Hierarchy

```
Collection
    └── Schema (defines data structure)
            └── Template (reusable data, optional)
                    └── Asset (the actual NFT)
```

### Collections

Top-level containers that group related NFTs. Authorization is per-collection, not per-author.

| Field | Description |
|-------|-------------|
| `collection_name` | Unique name (1-12 chars, a-z, 1-5) |
| `author` | Creator account |
| `allow_notify` | Enable contract notifications |
| `authorized_accounts` | Accounts that can create assets |
| `notify_accounts` | Accounts to notify on transfers |
| `market_fee` | Marketplace fee percentage |

### Schemas

Define the data structure for NFTs in a collection.

| Field | Description |
|-------|-------------|
| `schema_name` | Unique within collection |
| `format` | Array of `{name, type}` attribute definitions |

Supported types: `int8`, `int16`, `int32`, `int64`, `uint8`, `uint16`, `uint32`, `uint64`, `float`, `double`, `string`, `image`, `ipfs`, `bool`

### Templates

Reusable data containers - multiple assets can share one template. This saves RAM when minting many similar NFTs.

| Field | Description |
|-------|-------------|
| `template_id` | Auto-generated ID |
| `schema_name` | Schema this template uses |
| `immutable_data` | Fixed data (cannot be changed) |
| `transferable` | Can assets be transferred? |
| `burnable` | Can assets be burned? |
| `max_supply` | Maximum mintable (0 = unlimited) |

### Assets

The actual NFTs owned by users.

| Field | Description |
|-------|-------------|
| `asset_id` | Unique 64-bit ID |
| `collection_name` | Parent collection |
| `schema_name` | Schema defining structure |
| `template_id` | Optional template reference |
| `immutable_data` | Fixed at creation |
| `mutable_data` | Can be updated by authorized accounts |

---

## API Endpoints

### AtomicAssets API

| Network | Endpoint | Provider |
|---------|----------|----------|
| Mainnet | `https://xpr.api.atomicassets.io` | Pink.gg |
| Mainnet | `https://aa-xprnetwork-main.saltant.io` | Saltant |
| Testnet | `https://test.xpr.api.atomicassets.io` | Pink.gg |
| Testnet | `https://aa-xprnetwork-test.saltant.io` | Saltant |

### AtomicMarket API (Marketplace)

| Network | Endpoint |
|---------|----------|
| Mainnet | `https://xpr.api.atomicassets.io` |

---

## Querying NFTs

### Get Assets Owned by Account

```typescript
async function getOwnedAssets(owner: string, collection?: string) {
  const params = new URLSearchParams({
    owner,
    limit: '100',
    order: 'desc',
    sort: 'asset_id'
  });

  if (collection) {
    params.set('collection_name', collection);
  }

  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/assets?${params}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Collection Info

```typescript
async function getCollection(collectionName: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/collections/${collectionName}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Templates in Collection

```typescript
async function getTemplates(collectionName: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/templates?collection_name=${collectionName}&limit=100`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Schemas in Collection

```typescript
async function getSchemas(collectionName: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/schemas?collection_name=${collectionName}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Specific Asset

```typescript
async function getAsset(assetId: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/assets/${assetId}`
  );
  const { data } = await response.json();
  return data;
}
```

---

## Marketplace Queries

### Get Active Sales

```typescript
async function getSales(collection?: string) {
  const params = new URLSearchParams({
    state: '1',  // 1 = listed/active
    limit: '100',
    order: 'desc',
    sort: 'created'
  });

  if (collection) {
    params.set('collection_name', collection);
  }

  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicmarket/v1/sales?${params}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Floor Price for Template

```typescript
async function getTemplateFloorPrice(templateId: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicmarket/v1/sales?` +
    `template_id=${templateId}&state=1&limit=1&order=asc&sort=price`
  );
  const { data } = await response.json();
  return data[0]?.price ?? null;
}
```

### Get Sales History

```typescript
async function getSalesHistory(assetId: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicmarket/v1/sales?` +
    `asset_id=${assetId}&state=3&limit=10`  // state 3 = sold
  );
  const { data } = await response.json();
  return data;
}
```

---

## Creating NFTs (Transactions)

### 1. Create Collection

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createcol',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    author: author,
    collection_name: 'mycollection',
    allow_notify: true,
    authorized_accounts: [author],
    notify_accounts: [],
    market_fee: 0.05,  // 5%
    data: []  // Collection metadata
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 2. Create Schema

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createschema',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_creator: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    schema_format: [
      { name: 'name', type: 'string' },
      { name: 'image', type: 'ipfs' },
      { name: 'description', type: 'string' },
      { name: 'rarity', type: 'string' },
      { name: 'power', type: 'uint32' }
    ]
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 3. Create Template

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createtempl',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_creator: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    transferable: true,
    burnable: true,
    max_supply: 1000,  // 0 = unlimited
    immutable_data: [
      { key: 'name', value: ['string', 'Epic Sword'] },
      { key: 'image', value: ['string', 'QmXxx...'] },  // IPFS hash
      { key: 'description', value: ['string', 'A legendary weapon'] },
      { key: 'rarity', value: ['string', 'epic'] },
      { key: 'power', value: ['uint32', 150] }
    ]
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 4. Mint Asset

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'mintasset',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_minter: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    template_id: 12345,  // From createtempl, or -1 for no template
    new_asset_owner: recipient,
    immutable_data: [],  // Additional immutable data
    mutable_data: [],    // Mutable data (can be updated later)
    tokens_to_back: []   // Optional token backing
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 5. Transfer Asset

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'transfer',
  authorization: [{ actor: owner, permission: 'active' }],
  data: {
    from: owner,
    to: recipient,
    asset_ids: ['1099512345678'],  // Array of asset IDs
    memo: 'Gift for you!'
  }
}];

await session.transact({ actions }, { broadcast: true });
```

---

## Marketplace Actions

### List Asset for Sale

```typescript
const actions = [{
  account: 'atomicmarket',
  name: 'announcesale',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    seller: seller,
    asset_ids: ['1099512345678'],
    listing_price: '100.0000 XPR',
    settlement_symbol: '4,XPR',
    maker_marketplace: ''  // Optional marketplace account
  }
},
{
  account: 'atomicassets',
  name: 'createoffer',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    sender: seller,
    recipient: 'atomicmarket',
    sender_asset_ids: ['1099512345678'],
    recipient_asset_ids: [],
    memo: 'sale'
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### Cancel Sale

```typescript
const actions = [{
  account: 'atomicmarket',
  name: 'cancelsale',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    sale_id: 12345
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### Purchase Asset

```typescript
const actions = [{
  account: 'eosio.token',
  name: 'transfer',
  authorization: [{ actor: buyer, permission: 'active' }],
  data: {
    from: buyer,
    to: 'atomicmarket',
    quantity: '100.0000 XPR',
    memo: 'deposit'
  }
},
{
  account: 'atomicmarket',
  name: 'purchasesale',
  authorization: [{ actor: buyer, permission: 'active' }],
  data: {
    buyer: buyer,
    sale_id: 12345,
    intended_delphi_median: 0,
    taker_marketplace: ''
  }
}];

await session.transact({ actions }, { broadcast: true });
```

---

## Smart Contract Integration

### Receiving NFT Notifications

To have your contract notified when assets are transferred:

1. Add your contract to collection's `notify_accounts`
2. Handle the notification in your contract:

```typescript
@action("transfer", notify)
onNFTTransfer(
  from: Name,
  to: Name,
  asset_ids: u64[],
  memo: string
): void {
  // Only process transfers TO this contract
  if (to != this.receiver) return;

  // Process each asset
  for (let i = 0; i < asset_ids.length; i++) {
    const assetId = asset_ids[i];
    // Handle the received NFT
    this.processReceivedNFT(from, assetId, memo);
  }
}
```

### Querying Assets On-Chain

```typescript
// Query atomicassets tables directly
const { rows } = await rpc.get_table_rows({
  code: 'atomicassets',
  scope: owner,  // Owner account as scope
  table: 'assets',
  limit: 100
});
```

---

## Data Serialization Format

AtomicAssets uses a custom serialization format for `immutable_data` and `mutable_data`:

```typescript
// Format: Array of { key: string, value: [type, data] }

const data = [
  { key: 'name', value: ['string', 'My NFT'] },
  { key: 'image', value: ['string', 'QmXxxIPFSHash'] },
  { key: 'power', value: ['uint32', 100] },
  { key: 'is_special', value: ['uint8', 1] }  // boolean as uint8
];
```

### Type Mapping

| Schema Type | Serialization Type |
|-------------|-------------------|
| `string` | `['string', 'value']` |
| `ipfs` | `['string', 'QmHash']` |
| `image` | `['string', 'url_or_ipfs']` |
| `uint8` - `uint64` | `['uint8', number]` etc. |
| `int8` - `int64` | `['int8', number]` etc. |
| `float` | `['float32', number]` |
| `double` | `['float64', number]` |
| `bool` | `['uint8', 0 or 1]` |

---

## Common Patterns

### Check if User Owns Asset

```typescript
async function userOwnsAsset(owner: string, assetId: string): Promise<boolean> {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/assets/${assetId}`
  );
  const { data } = await response.json();
  return data?.owner === owner;
}
```

### Get All Assets with Metadata

```typescript
async function getAssetsWithMetadata(owner: string) {
  const response = await fetch(
    `https://xpr.api.atomicassets.io/atomicassets/v1/assets?owner=${owner}&limit=100`
  );
  const { data } = await response.json();

  return data.map(asset => ({
    id: asset.asset_id,
    name: asset.data?.name ?? asset.template?.immutable_data?.name,
    image: asset.data?.image ?? asset.template?.immutable_data?.image,
    collection: asset.collection.collection_name,
    schema: asset.schema.schema_name,
    template_id: asset.template?.template_id,
    ...asset.data
  }));
}
```

### Batch Mint Multiple Assets

```typescript
async function batchMint(
  author: string,
  collection: string,
  schema: string,
  templateId: number,
  recipients: string[]
) {
  const actions = recipients.map(recipient => ({
    account: 'atomicassets',
    name: 'mintasset',
    authorization: [{ actor: author, permission: 'active' }],
    data: {
      authorized_minter: author,
      collection_name: collection,
      schema_name: schema,
      template_id: templateId,
      new_asset_owner: recipient,
      immutable_data: [],
      mutable_data: [],
      tokens_to_back: []
    }
  }));

  // Note: Transaction size limits apply (~100 mints per tx)
  await session.transact({ actions }, { broadcast: true });
}
```

---

## IPFS for NFT Media

Store images and metadata on IPFS:

### Pinata (Recommended)

```typescript
async function uploadToIPFS(file: File): Promise<string> {
  const formData = new FormData();
  formData.append('file', file);

  const response = await fetch('https://api.pinata.cloud/pinning/pinFileToIPFS', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${PINATA_JWT}`
    },
    body: formData
  });

  const { IpfsHash } = await response.json();
  return IpfsHash;  // Use this as 'image' value
}
```

### IPFS Gateways

| Gateway | URL Pattern |
|---------|-------------|
| Pinata | `https://gateway.pinata.cloud/ipfs/{hash}` |
| IPFS.io | `https://ipfs.io/ipfs/{hash}` |

---

## Fees and Costs

### RAM Costs

| Operation | RAM (bytes) |
|-----------|-------------|
| Create collection | ~300 |
| Create schema | ~150 + attributes |
| Create template | ~200 + data size |
| Mint asset | ~151 + data size |

RAM is paid by the minter/creator, not the recipient.

### Marketplace Fees

- **Collection fee**: Set by collection creator (typically 2-10%)
- **Marketplace fee**: Set by marketplace (typically 1-2%)
- Fees are taken from sale price when asset sells

---

## Resources

- **AtomicAssets Docs**: https://github.com/pinknetworkx/atomicassets-contract
- **AtomicMarket Docs**: https://github.com/pinknetworkx/atomicmarket-contract
- **API Documentation**: https://xpr.api.atomicassets.io/docs
- **XPR Market Reference**: https://github.com/XPRNetwork/xpr-market

## Practical Learnings (Real-World Gotchas)

These are hard-won lessons from building an NFT marketplace and minting 500+ NFTs on XPR Network mainnet.

### Registering Your Own Marketplace

Register to earn maker/taker fees (1% each by default) on sales through your marketplace:

```bash
proton action atomicmarket regmarket '{"creator":"youraccount","marketplace_name":"youraccount"}' youraccount
```

Then use your marketplace name in `announcesale` (maker_marketplace) and `purchasesale` (taker_marketplace) to earn fees.

### Listing For Sale — Two Actions, One Transaction

`announcesale` and `createoffer` MUST be in the same transaction. If done separately, the API can get out of sync — the sale record exists but the asset never moves to escrow.

```typescript
const actions = [
  {
    account: 'atomicmarket',
    name: 'announcesale',
    authorization: [{ actor: seller, permission: 'active' }],
    data: {
      seller,
      asset_ids: [assetId],
      listing_price: '100.0000 XPR',  // Exactly 4 decimal places for XPR
      settlement_symbol: '4,XPR',
      maker_marketplace: 'youraccount',
    },
  },
  {
    account: 'atomicassets',
    name: 'createoffer',
    authorization: [{ actor: seller, permission: 'active' }],
    data: {
      sender: seller,
      recipient: 'atomicmarket',
      sender_asset_ids: [assetId],
      recipient_asset_ids: [],
      memo: 'sale',
    },
  },
];
// Submit BOTH actions in a single transact() call
```

### Price Formatting — API Returns Raw Integers

The AtomicMarket API returns `listing_price` as a raw integer string, NOT a formatted asset string:

```
API returns:  "listing_price": "100000"  (raw)
This means:   10.0000 XPR  (divide by 10^precision)
XPR precision: 4  →  divide by 10000
XUSDC precision: 6  →  divide by 1000000
```

For buy transactions, format back as asset string: `"10.0000 XPR"`

### Getting Template ID After Creation

Do NOT query the API immediately after `createtempl` — there's an indexing delay. Instead, extract the template ID from the transaction's inline `lognewtempl` trace:

```typescript
const result = await session.transact({ actions: [createTemplAction] });
// Find lognewtempl in inline traces
const trace = result.processed.action_traces[0];
for (const inline of trace.inline_traces || []) {
  if (inline.act.name === 'lognewtempl') {
    const templateId = inline.act.data.template_id;
    // Use this templateId for minting — it's guaranteed correct
  }
}
```

### Batch Minting — RAM Management

When minting many NFTs in sequence, you'll hit RAM limits. Buy RAM proactively:

```bash
proton action eosio buyram '{"payer":"youraccount","receiver":"youraccount","quant":"500.0000 XPR"}' youraccount
```

Each NFT asset costs ~151 bytes. For 500 NFTs, budget ~75,000 bytes of RAM.

If a mint fails with "has X bytes has Y bytes", buy more RAM and retry. Don't retry the failed mint without buying RAM first.

### Airdrop Patterns

**Mint directly to recipients** (most efficient):
```typescript
// Mint NFT directly to the recipient's wallet
const action = {
  account: 'atomicassets',
  name: 'mintasset',
  data: {
    authorized_minter: 'youraccount',
    collection_name: 'yourcollect1',
    schema_name: 'myschema',
    template_id: templateId,
    new_asset_owner: recipientAccount,  // Goes directly to them
    immutable_data: [],
    mutable_data: [],
    tokens_to_back: [],
  },
};
```

**Token holder airdrop** — query asset owners from AtomicAssets API:
```
GET https://xpr.api.atomicassets.io/atomicassets/v1/accounts?collection_name=COLLECTION
```
Returns unique account names that own assets in the collection. To get owners of a specific template:
```
GET https://xpr.api.atomicassets.io/atomicassets/v1/assets?template_id=TEMPLATE_ID&limit=100
```
Extract unique `owner` fields, then mint to each.

### IPFS Gateway Selection

- **Upload**: Use Pinata API (`api.pinata.cloud/pinning/pinFileToIPFS`) with JWT
- **Display**: Use `ipfs.io/ipfs/{hash}` — works for ALL content, not just yours
- **Don't use** private gateways (e.g. `agent.mypinata.cloud`) for display — returns 403 for content not pinned on your account
- Store ONLY the IPFS hash in NFT data, not the full gateway URL

### Collection Market Fee

Set `market_fee` when creating collections. This fee is taken from EVERY sale on ANY marketplace:

```bash
# 5% collection fee (0.05)
proton action atomicassets createcol '{"author":"you","collection_name":"yourcollect1",...,"market_fee":0.05,...}' you
```

The fee goes to the collection author. Combined with marketplace fees (1% maker + 1% taker), a sale through your marketplace earns: collection_fee + maker_fee + taker_fee.

### Rich NFT Attributes

Use schemas to define typed attributes that are searchable and filterable:

```typescript
const schemaFormat = [
  { name: 'name', type: 'string' },
  { name: 'img', type: 'string' },        // IPFS hash
  { name: 'description', type: 'string' },
  { name: 'rarity', type: 'string' },      // "legendary", "rare", etc
  { name: 'score', type: 'uint32' },        // Numeric attributes
  { name: 'generation_date', type: 'string' },
];
```

Store data-rich attributes in templates (immutable) for NFTs that tell a story. The more attributes, the more interesting the NFT becomes for collectors and tools.

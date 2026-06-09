# Payment Patterns and Commerce Integration

This guide covers building payment systems, invoicing, and e-commerce integration on XPR Network.

## Overview

XPR Network is ideal for payments due to:
- **Zero gas fees** - Recipients get full amount
- **Fast finality** - ~2 second confirmation
- **Human-readable accounts** - Easy to share (@merchant)
- **Memo field** - Attach order IDs, invoices, metadata

---

## Payment Links

### Simple Payment Link

Generate shareable links for receiving payments:

```typescript
interface PaymentLink {
  recipient: string;
  amount?: string;      // Optional pre-filled amount
  token?: string;       // Default: XPR
  contract?: string;    // Default: eosio.token
  memo?: string;        // Order ID, invoice number
}

function generatePaymentLink(params: PaymentLink): string {
  const base = 'https://webauth.com/pay';
  const url = new URL(base);

  url.searchParams.set('to', params.recipient);

  if (params.amount) {
    url.searchParams.set('amount', params.amount);
  }
  if (params.token) {
    url.searchParams.set('token', params.token);
  }
  if (params.contract) {
    url.searchParams.set('contract', params.contract);
  }
  if (params.memo) {
    url.searchParams.set('memo', params.memo);
  }

  return url.toString();
}

// Examples
const simpleLink = generatePaymentLink({
  recipient: 'merchant'
});
// https://webauth.com/pay?to=merchant

const invoiceLink = generatePaymentLink({
  recipient: 'merchant',
  amount: '25.0000',
  token: 'XPR',
  memo: 'INV-2024-001'
});
// https://webauth.com/pay?to=merchant&amount=25.0000&token=XPR&memo=INV-2024-001

const usdcLink = generatePaymentLink({
  recipient: 'merchant',
  amount: '100.000000',
  token: 'XUSDC',
  contract: 'xtokens',
  memo: 'ORDER-12345'
});
```

### QR Code Generation

```typescript
import QRCode from 'qrcode';

async function generatePaymentQR(params: PaymentLink): Promise<string> {
  const link = generatePaymentLink(params);
  return QRCode.toDataURL(link);
}

// React component
function PaymentQR({ recipient, amount, memo }: PaymentLink) {
  const [qrDataUrl, setQrDataUrl] = useState<string>('');

  useEffect(() => {
    generatePaymentQR({ recipient, amount, memo })
      .then(setQrDataUrl);
  }, [recipient, amount, memo]);

  return <img src={qrDataUrl} alt="Payment QR Code" />;
}
```

---

## Invoice System

### Invoice Data Structure

```typescript
interface Invoice {
  id: string;
  merchant: string;
  customer?: string;
  items: InvoiceItem[];
  subtotal: number;
  tax: number;
  total: number;
  currency: string;
  status: 'pending' | 'paid' | 'expired' | 'cancelled';
  createdAt: Date;
  expiresAt?: Date;
  paidAt?: Date;
  txId?: string;
  memo: string;  // Unique identifier for matching
}

interface InvoiceItem {
  description: string;
  quantity: number;
  unitPrice: number;
  total: number;
}
```

### Generate Invoice Memo

Use structured memos to match payments to invoices:

```typescript
// Simple format
const memo = `INV-${invoiceId}`;

// Structured format (parseable)
const memo = JSON.stringify({
  type: 'invoice',
  id: invoiceId,
  merchant: 'mystore'
});

// Short hash format (for privacy)
import crypto from 'crypto';

function generateInvoiceMemo(invoiceId: string, secret: string): string {
  const hash = crypto
    .createHmac('sha256', secret)
    .update(invoiceId)
    .digest('hex')
    .slice(0, 16);
  return `PAY-${hash}`;
}
```

### Invoice Service

```typescript
class InvoiceService {
  private db: Database;
  private secret: string;

  constructor(db: Database, secret: string) {
    this.db = db;
    this.secret = secret;
  }

  async createInvoice(params: {
    merchant: string;
    items: InvoiceItem[];
    currency: string;
    expiresInMinutes?: number;
  }): Promise<Invoice> {
    const id = crypto.randomUUID();
    const subtotal = params.items.reduce((sum, item) => sum + item.total, 0);
    const tax = subtotal * 0.1;  // 10% tax example
    const total = subtotal + tax;

    const invoice: Invoice = {
      id,
      merchant: params.merchant,
      items: params.items,
      subtotal,
      tax,
      total,
      currency: params.currency,
      status: 'pending',
      createdAt: new Date(),
      expiresAt: params.expiresInMinutes
        ? new Date(Date.now() + params.expiresInMinutes * 60000)
        : undefined,
      memo: this.generateMemo(id)
    };

    await this.db.invoices.insert(invoice);
    return invoice;
  }

  private generateMemo(invoiceId: string): string {
    return `INV-${invoiceId.slice(0, 8).toUpperCase()}`;
  }

  async getPaymentLink(invoiceId: string): Promise<string> {
    const invoice = await this.db.invoices.findOne({ id: invoiceId });
    if (!invoice) throw new Error('Invoice not found');

    const precision = invoice.currency === 'XPR' ? 4 : 6;
    const amount = invoice.total.toFixed(precision);

    return generatePaymentLink({
      recipient: invoice.merchant,
      amount,
      token: invoice.currency,
      contract: invoice.currency === 'XPR' ? 'eosio.token' : 'xtokens',
      memo: invoice.memo
    });
  }

  async matchPayment(transfer: {
    from: string;
    to: string;
    quantity: string;
    memo: string;
    txId: string;
  }): Promise<Invoice | null> {
    // Find invoice by memo
    const invoice = await this.db.invoices.findOne({
      memo: transfer.memo,
      merchant: transfer.to,
      status: 'pending'
    });

    if (!invoice) return null;

    // Parse amount
    const [amountStr, symbol] = transfer.quantity.split(' ');
    const amount = parseFloat(amountStr);

    // Verify amount matches (with small tolerance for rounding)
    if (Math.abs(amount - invoice.total) > 0.0001) {
      console.warn(`Amount mismatch: expected ${invoice.total}, got ${amount}`);
      return null;
    }

    // Mark as paid
    invoice.status = 'paid';
    invoice.paidAt = new Date();
    invoice.txId = transfer.txId;
    invoice.customer = transfer.from;

    await this.db.invoices.update({ id: invoice.id }, invoice);
    return invoice;
  }
}
```

### Payment Watcher

```typescript
class PaymentWatcher {
  private invoiceService: InvoiceService;
  private poller: ActionPoller;

  constructor(invoiceService: InvoiceService, merchantAccount: string) {
    this.invoiceService = invoiceService;
    this.poller = new ActionPoller(merchantAccount, 'eosio.token:transfer', 3000);
  }

  start(onPayment: (invoice: Invoice) => void): void {
    this.poller.start(async (actions) => {
      for (const action of actions) {
        // Only process incoming transfers
        if (action.act.data.to !== this.merchantAccount) continue;

        const invoice = await this.invoiceService.matchPayment({
          from: action.act.data.from,
          to: action.act.data.to,
          quantity: action.act.data.quantity,
          memo: action.act.data.memo,
          txId: action.trx_id
        });

        if (invoice) {
          onPayment(invoice);
        }
      }
    });
  }
}

// Usage
const watcher = new PaymentWatcher(invoiceService, 'merchant');
watcher.start((invoice) => {
  console.log(`Invoice ${invoice.id} paid by ${invoice.customer}`);
  // Send confirmation email, update order status, etc.
});
```

---

## Point of Sale (POS)

### POS Terminal Component

```tsx
import { useState, useEffect } from 'react';

interface POSProps {
  merchant: string;
  onPaymentReceived: (payment: any) => void;
}

function POSTerminal({ merchant, onPaymentReceived }: POSProps) {
  const [amount, setAmount] = useState('');
  const [currency, setCurrency] = useState('XPR');
  const [memo, setMemo] = useState('');
  const [showQR, setShowQR] = useState(false);
  const [qrUrl, setQrUrl] = useState('');

  const generateQR = async () => {
    const invoiceMemo = memo || `POS-${Date.now()}`;
    const precision = currency === 'XPR' ? 4 : 6;

    const link = generatePaymentLink({
      recipient: merchant,
      amount: parseFloat(amount).toFixed(precision),
      token: currency,
      contract: currency === 'XPR' ? 'eosio.token' : 'xtokens',
      memo: invoiceMemo
    });

    const qr = await QRCode.toDataURL(link);
    setQrUrl(qr);
    setShowQR(true);

    // Start watching for payment
    watchForPayment(merchant, invoiceMemo, onPaymentReceived);
  };

  return (
    <div className="pos-terminal">
      {!showQR ? (
        <div className="pos-input">
          <input
            type="number"
            placeholder="Amount"
            value={amount}
            onChange={(e) => setAmount(e.target.value)}
          />
          <select value={currency} onChange={(e) => setCurrency(e.target.value)}>
            <option value="XPR">XPR</option>
            <option value="XUSDC">XUSDC</option>
            <option value="XUSDT">XUSDT</option>
          </select>
          <input
            type="text"
            placeholder="Reference (optional)"
            value={memo}
            onChange={(e) => setMemo(e.target.value)}
          />
          <button onClick={generateQR}>Generate Payment</button>
        </div>
      ) : (
        <div className="pos-qr">
          <img src={qrUrl} alt="Payment QR" />
          <p>Scan to pay {amount} {currency}</p>
          <button onClick={() => setShowQR(false)}>Cancel</button>
        </div>
      )}
    </div>
  );
}
```

---

## Recurring Payments / Subscriptions

XPR Network doesn't have native recurring payments, but you can implement them with authorization patterns.

### Subscription Contract

```typescript
import {
  Contract, Table, TableStore, Name, Asset,
  InlineAction, PermissionLevel, check, requireAuth,
  currentTimeSec
} from 'proton-tsc';

@table("subscriptions")
class Subscription extends Table {
  constructor(
    public id: u64 = 0,
    public subscriber: Name = new Name(),
    public merchant: Name = new Name(),
    public amount: u64 = 0,
    public symbol: string = "",
    public interval: u64 = 0,      // seconds between charges
    public lastCharged: u64 = 0,
    public nextCharge: u64 = 0,
    public active: boolean = true
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }

  @secondary
  get bySubscriber(): u64 { return this.subscriber.N; }

  @secondary
  get byNextCharge(): u64 { return this.nextCharge; }
}

@contract
class SubscriptionManager extends Contract {
  subsTable: TableStore<Subscription> = new TableStore<Subscription>(this.receiver);

  // User creates subscription (authorizes recurring charges)
  @action("subscribe")
  subscribe(
    subscriber: Name,
    merchant: Name,
    amount: Asset,
    intervalDays: u32
  ): void {
    requireAuth(subscriber);

    const now = currentTimeSec();
    const interval = intervalDays * 86400;

    const sub = new Subscription(
      this.subsTable.availablePrimaryKey,
      subscriber,
      merchant,
      amount.amount,
      amount.symbol.toString(),
      interval,
      now,
      now + interval,
      true
    );

    this.subsTable.store(sub, subscriber);
  }

  // User cancels subscription
  @action("unsubscribe")
  unsubscribe(subscriber: Name, subscriptionId: u64): void {
    requireAuth(subscriber);

    const sub = this.subsTable.requireGet(subscriptionId, "Subscription not found");
    check(sub.subscriber == subscriber, "Not your subscription");

    sub.active = false;
    this.subsTable.update(sub, subscriber);
  }

  // Merchant or bot charges due subscriptions
  @action("charge")
  charge(subscriptionId: u64): void {
    const sub = this.subsTable.requireGet(subscriptionId, "Subscription not found");
    check(sub.active, "Subscription not active");

    const now = currentTimeSec();
    check(now >= sub.nextCharge, "Not yet due");

    // Transfer from subscriber to merchant
    // Note: Subscriber must have granted permission to this contract

    sub.lastCharged = now;
    sub.nextCharge = now + sub.interval;
    this.subsTable.update(sub, this.receiver);
  }

  // Bot calls this to process all due subscriptions
  @action("processdue")
  processDue(limit: u32): void {
    const now = currentTimeSec();
    let processed: u32 = 0;

    // Query by nextCharge index
    const cursor = this.subsTable.lowerBound(0);  // Would need proper index query

    // Process due subscriptions
    // (Simplified - actual implementation needs secondary index iteration)
  }
}
```

### Subscription Bot

```typescript
class SubscriptionBot {
  private interval: NodeJS.Timer | null = null;

  async start(): Promise<void> {
    // Run every hour
    this.interval = setInterval(() => this.processDue(), 3600000);
    await this.processDue();
  }

  private async processDue(): Promise<void> {
    try {
      // Get due subscriptions
      const { rows } = await rpc.get_table_rows({
        code: 'subsmanager',
        scope: 'subsmanager',
        table: 'subscriptions',
        index_position: 'tertiary',  // byNextCharge
        key_type: 'i64',
        upper_bound: Math.floor(Date.now() / 1000),
        limit: 100
      });

      for (const sub of rows) {
        if (!sub.active) continue;

        await api.transact({
          actions: [{
            account: 'subsmanager',
            name: 'charge',
            authorization: [{ actor: 'subsbot', permission: 'active' }],
            data: { subscriptionId: sub.id }
          }]
        });

        console.log(`Charged subscription ${sub.id}`);
      }
    } catch (error) {
      console.error('Process due error:', error);
    }
  }

  stop(): void {
    if (this.interval) {
      clearInterval(this.interval);
    }
  }
}
```

---

## Payment Confirmation Page

### React Component

```tsx
import { useState, useEffect } from 'react';

interface PaymentConfirmationProps {
  invoiceId: string;
}

function PaymentConfirmation({ invoiceId }: PaymentConfirmationProps) {
  const [status, setStatus] = useState<'pending' | 'paid' | 'expired'>('pending');
  const [invoice, setInvoice] = useState<Invoice | null>(null);

  useEffect(() => {
    // Fetch invoice
    fetchInvoice(invoiceId).then(setInvoice);

    // Poll for payment
    const interval = setInterval(async () => {
      const updated = await fetchInvoice(invoiceId);
      setInvoice(updated);

      if (updated.status === 'paid') {
        setStatus('paid');
        clearInterval(interval);
      } else if (updated.expiresAt && new Date() > new Date(updated.expiresAt)) {
        setStatus('expired');
        clearInterval(interval);
      }
    }, 3000);

    return () => clearInterval(interval);
  }, [invoiceId]);

  if (!invoice) return <div>Loading...</div>;

  return (
    <div className="payment-confirmation">
      {status === 'pending' && (
        <>
          <h2>Awaiting Payment</h2>
          <p>Amount: {invoice.total} {invoice.currency}</p>
          <PaymentQR
            recipient={invoice.merchant}
            amount={invoice.total.toFixed(4)}
            memo={invoice.memo}
          />
          <p>Or send to: @{invoice.merchant}</p>
          <p>Memo: {invoice.memo}</p>
          {invoice.expiresAt && (
            <p>Expires: <Countdown to={invoice.expiresAt} /></p>
          )}
        </>
      )}

      {status === 'paid' && (
        <div className="success">
          <h2>Payment Received!</h2>
          <p>Thank you for your payment.</p>
          <p>Transaction: {invoice.txId}</p>
          <a href={`https://explorer.xprnetwork.org/transaction/${invoice.txId}`}>
            View on Explorer
          </a>
        </div>
      )}

      {status === 'expired' && (
        <div className="expired">
          <h2>Invoice Expired</h2>
          <p>This invoice has expired. Please request a new one.</p>
        </div>
      )}
    </div>
  );
}
```

---

## E-commerce Integration

### Checkout Flow

```typescript
// 1. Create order in your system
const order = await createOrder({
  items: cart.items,
  customer: customerInfo,
  shippingAddress: address
});

// 2. Create invoice
const invoice = await invoiceService.createInvoice({
  merchant: 'mystore',
  items: order.items.map(item => ({
    description: item.name,
    quantity: item.quantity,
    unitPrice: item.price,
    total: item.quantity * item.price
  })),
  currency: 'XUSDC',
  expiresInMinutes: 30
});

// 3. Associate invoice with order
await updateOrder(order.id, { invoiceId: invoice.id });

// 4. Redirect to payment page
redirect(`/pay/${invoice.id}`);

// 5. Handle payment webhook
app.post('/webhooks/payment', async (req, res) => {
  const { invoiceId } = req.body;

  const invoice = await invoiceService.getInvoice(invoiceId);
  if (invoice.status !== 'paid') return res.status(400).send('Not paid');

  const order = await getOrderByInvoice(invoiceId);

  // Update order status
  await updateOrder(order.id, { status: 'paid', paidAt: new Date() });

  // Send confirmation email
  await sendOrderConfirmation(order);

  // Trigger fulfillment
  await startFulfillment(order);

  res.send('OK');
});
```

### Multi-Currency Support

```typescript
const SUPPORTED_TOKENS = {
  XPR: { contract: 'eosio.token', precision: 4 },
  XUSDC: { contract: 'xtokens', precision: 6 },
  XUSDT: { contract: 'xtokens', precision: 6 },
  XBTC: { contract: 'xtokens', precision: 8 }
};

async function createMultiCurrencyInvoice(
  merchant: string,
  amountUSD: number
): Promise<{ [currency: string]: string }> {
  const links: { [currency: string]: string } = {};

  // Get current prices
  const xprPrice = await getOraclePrice(1);

  for (const [symbol, config] of Object.entries(SUPPORTED_TOKENS)) {
    let amount: number;

    if (symbol === 'XUSDC' || symbol === 'XUSDT') {
      amount = amountUSD;  // Stablecoins
    } else if (symbol === 'XPR') {
      amount = amountUSD / xprPrice;
    } else {
      continue;  // Skip non-supported
    }

    links[symbol] = generatePaymentLink({
      recipient: merchant,
      amount: amount.toFixed(config.precision),
      token: symbol,
      contract: config.contract,
      memo: `INV-${Date.now()}`
    });
  }

  return links;
}
```

---

## Quick Reference

### Payment Link Format

```
https://webauth.com/pay?to=ACCOUNT&amount=AMOUNT&token=TOKEN&contract=CONTRACT&memo=MEMO
```

### Common Token Configurations

| Token | Contract | Precision | Type |
|-------|----------|-----------|------|
| XPR | `eosio.token` | 4 | Native |
| XUSDC | `xtokens` | 6 | Stablecoin |
| XUSDT | `xtokens` | 6 | Stablecoin |
| XBTC | `xtokens` | 8 | Wrapped |

### Memo Best Practices

| Use Case | Format | Example |
|----------|--------|---------|
| Invoice | `INV-{id}` | `INV-ABC123` |
| Order | `ORDER-{id}` | `ORDER-12345` |
| POS | `POS-{timestamp}` | `POS-1705123456` |
| Donation | `DONATE-{campaign}` | `DONATE-CHARITY` |
| Tip | `TIP-{username}` | `TIP-alice` |

### Integration Checklist

- [ ] Generate unique memos for each transaction
- [ ] Implement payment matching logic
- [ ] Handle partial payments (if applicable)
- [ ] Set appropriate expiration times
- [ ] Send payment confirmations
- [ ] Log all transactions for accounting
- [ ] Test with small amounts first
- [ ] Handle network errors gracefully

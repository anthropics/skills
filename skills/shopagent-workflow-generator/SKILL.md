---
name: shopagent-workflow-generator
description: Generate AI-powered Shopify workflow packs for any automation use case using the ShopAgent API. Use when the user wants to automate Shopify tasks, create workflow packs, set up order routing, manage inventory, segment customers, recover abandoned carts, or orchestrate product launches.
version: 1.0.0
author: mrmderrico@gmail.com
argument-hint: "[use case or workflow description]"
---

# ShopAgent Workflow Generator

Generate AI-powered Shopify workflow packs via the ShopAgent API at https://getshopagent.com.

## API Details

- **Endpoint:** `https://getshopagent.com/api/generate`
- **Method:** POST
- **Auth:** `Authorization: Bearer <SHOPAGENT_API_KEY>`
- **Content-Type:** `application/json`

## How to Generate a Workflow Pack

1. Ask the user for their ShopAgent API key if not already provided (or check `$SHOPAGENT_API_KEY` env var).
2. Clarify the workflow use case from `$ARGUMENTS` or by asking the user.
3. Build the request payload with a clear `prompt` describing the desired automation.
4. Call the API using Bash with curl (see request format below).
5. Parse the JSON response and present the workflow pack steps to the user.
6. Ask if the user wants to refine, export, or install the workflow into their Shopify store.

## Request Format

```bash
curl -s -X POST https://getshopagent.com/api/generate \
  -H "Authorization: Bearer $SHOPAGENT_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"prompt": "<describe the workflow automation>"}'
```

## Response Handling

- On success (HTTP 200): parse and display the `workflow` object containing steps, triggers, and actions.
- On 401: inform the user their API key is invalid or missing.
- On 429: inform the user they have hit their rate limit and to try again shortly.
- On 5xx: report a ShopAgent service error and suggest retrying.

## 5 Common Workflow Examples

### 1. Inventory Management
**Use case:** Auto-reorder products when stock falls below a threshold.
```json
{"prompt": "Create a workflow that monitors inventory levels across all products. When any SKU drops below 10 units, automatically create a purchase order draft and notify the purchasing team via email with the product name, current stock, and supplier details."}
```

### 2. Order Routing
**Use case:** Route orders to the correct fulfillment center by region.
```json
{"prompt": "Create a workflow that routes incoming orders to fulfillment centers based on shipping address. Orders from ZIP codes 90000-96999 go to the West Coast warehouse; 10000-19999 go to the East Coast warehouse; all others go to the Central warehouse. Tag each order with its assigned warehouse."}
```

### 3. Customer Segmentation
**Use case:** Auto-tag customers by lifetime value and purchase behavior.
```json
{"prompt": "Create a workflow that segments customers after each completed order. Customers with lifetime value over $500 and 3+ orders get tagged 'VIP'. Customers with one order under $50 get tagged 'new'. Customers inactive for 90+ days get tagged 'at-risk'. Send each segment a personalized follow-up email."}
```

### 4. Abandoned Cart Recovery
**Use case:** Multi-step recovery sequence for abandoned carts.
```json
{"prompt": "Create an abandoned cart recovery workflow. 1 hour after abandonment, send a reminder email with the cart contents. If no purchase after 24 hours, send a second email with a 10% discount code. If still no purchase after 48 hours, send a final email with free shipping and the discount. Stop the sequence immediately upon purchase."}
```

### 5. Product Launch
**Use case:** Orchestrate a full product launch across channels.
```json
{"prompt": "Create a product launch workflow triggered when a product is set to 'active' with the tag 'launch'. Steps: (1) Send announcement email to subscriber list, (2) Post to Facebook and Instagram via social integrations, (3) Apply a 15% launch discount valid for 48 hours, (4) Notify the fulfillment team to prioritize stock, (5) Send a Slack alert to the marketing channel with the product URL."}
```

## Tips

- Be specific in your prompt: include triggers, conditions, actions, and notification targets.
- You can chain multiple automations by referencing prior workflow IDs in follow-up calls.
- All generated workflow packs are compatible with Shopify Flow and ShopAgent's own runner.
- For custom integrations not listed above, describe the trigger event and desired outcome in plain language.

# IntegrationHub

## Scope

Use this reference for IntegrationHub spokes, custom actions, Connection & Credential Aliases, Data Stream Actions, subflows, retry strategy, and external API integration patterns on the ServiceNow platform.

## Plugin and Role Assumptions

Clarify whether the environment uses:

- IntegrationHub only or packaged spokes
- REST, SOAP, JDBC, or Data Stream Actions
- Connection & Credential Aliases managed centrally or by each app team
- MID Servers for private network access
- external rate limits, webhook callbacks, or long-running polling patterns

Typical stakeholders are integration developers, platform admins, credential owners, and flow designers.

## Core Building Blocks

| Building Block | Use |
|----------------|-----|
| Connection & Credential Alias | decouple auth and config from script |
| Action | reusable integration step |
| Subflow | orchestration and reuse |
| Data Stream Action | paginated or streamed API ingestion |
| Spoke | packaged set of related actions |

## Recommended Design Order

1. Define external system contract
2. Configure connection alias and credentials
3. Build reusable actions
4. Wrap business orchestration in subflows or flows
5. Add retries, logging, and idempotency
6. Test with representative payloads

## Custom Action Script Step

```javascript
(function execute(inputs, outputs) {
    var baseUrl = gs.getProperty('x_scope.integration.base_url');
    if (gs.nil(baseUrl)) {
        throw new Error('Missing x_scope.integration.base_url property');
    }

    var rm = new sn_ws.RESTMessageV2();
    rm.setEndpoint(baseUrl + inputs.endpoint_path);
    rm.setHttpMethod('GET');
    rm.setRequestHeader('Accept', 'application/json');
    rm.setHttpTimeout(30000);

    var response = rm.execute();
    outputs.status_code = response.getStatusCode();
    outputs.body = response.getBody();

    if (outputs.status_code < 200 || outputs.status_code >= 300) {
        throw new Error('IntegrationHub action failed: ' + outputs.status_code);
    }
})(inputs, outputs);
```

If the customer already has a REST Message record with alias-backed authentication, prefer `new sn_ws.RESTMessageV2('message_name', 'method_name')` instead of rebuilding the transport layer in script.

## Idempotent Create Pattern

For create or sync actions, send a stable external key whenever the upstream API supports it.

```javascript
(function execute(inputs, outputs) {
    var rm = new sn_ws.RESTMessageV2('x_scope.vendor_api', 'create_record');
    rm.setRequestHeader('Idempotency-Key', inputs.idempotency_key);
    rm.setRequestBody(JSON.stringify({
        external_id: inputs.external_id,
        short_description: inputs.short_description
    }));

    var response = rm.execute();
    outputs.status_code = response.getStatusCode();
    outputs.body = response.getBody();
})(inputs, outputs);
```

## Data Stream Action Pattern

Use Data Stream Actions when:

- the source is paginated
- records arrive in large batches
- transformation must be incremental
- memory pressure matters

Document:

- page size
- cursor or offset strategy
- retry conditions
- terminal conditions

## Data Stream Cursor Guidance

For paginated sources, the action contract should expose:

- current cursor or offset
- next cursor returned by the upstream system
- whether the page is terminal
- retryable error conditions

Do not hide pagination state inside ad hoc script globals.

## Connection Strategy

Preferred patterns:

- Connection & Credential Aliases
- REST Message methods with configured auth
- property-backed non-secret config

Avoid:

- hardcoded usernames or passwords
- hardcoded OAuth profile sys_ids
- endpoint URLs duplicated across many scripts

## Error Handling

For resilient actions:

1. return clear outputs for status, body, and cursor
2. distinguish retryable vs non-retryable errors
3. log correlation IDs or upstream request IDs if available
4. make create or update calls idempotent where possible

## Retry and Rate Limits

Call out:

- 429 handling
- exponential backoff expectations
- upstream timeout behavior
- duplicate suppression

## Workflow Example: Action Plus Subflow

1. a reusable action handles transport, response parsing, and normalized outputs
2. a subflow decides whether to retry, create a follow-up task, or continue orchestration
3. business logic stays outside the transport action unless it is truly reusable
4. rate-limit and auth failures become explicit flow branches instead of generic script errors

## Troubleshooting

Common failure modes:

- the action works in test but fails in production because aliases or MID Server routing differ
- retries create duplicate records because no external key or idempotency strategy exists
- pagination loops indefinitely because the terminal condition is not explicit
- 429 or timeout behavior is treated like a hard failure instead of a retryable one
- downstream flows break because action outputs are renamed without versioning or documentation

## Testing Guidance

Good validation includes:

- happy path
- auth failure
- pagination
- malformed payload
- partial failure or retry
- duplicate create or update request
- MID Server or network path assumptions when applicable

## Best Practices

1. Keep credential ownership out of source control and inside aliases or configured connection records.
2. Separate transport concerns from business orchestration.
3. Prefer reusable actions over embedding full integration logic in many flows.
4. Write outputs explicitly so downstream flow steps are stable.
5. Explain the idempotency and retry story whenever proposing IntegrationHub automation.

---
name: vastai-sdk
description: Vast.ai Python SDK for renting on-demand GPU compute — train models, run inference, and manage cloud instances programmatically. Use when writing Python code that provisions or interacts with Vast.ai GPU instances, volumes, or serverless endpoints.
allowed-tools: Python(vastai:*)
compatibility: Python 3.9+
metadata:
  author: vast-ai
---

# Vast.ai Python SDK (`vastai` / `vastai_sdk`)

The `vastai` package provides a Python SDK for managing GPU instances, volumes, serverless endpoints, and billing on Vast.ai. The `vastai_sdk` package is a backward-compatibility shim that re-exports `vastai`.

## Installation

```bash
pip install vastai
```

For serverless and async support:
```bash
pip install "vastai[serverless]"
```

## Authentication

The SDK reads the API key from `~/.vast_api_key` by default. You can also pass it explicitly:

```python
from vastai import VastAI
vast = VastAI()                        # reads ~/.vast_api_key
vast = VastAI(api_key="YOUR_API_KEY")  # explicit key
```

Get your API key from https://console.vast.ai/manage-keys/

## Backward Compatibility

The old `vastai_sdk` import still works:

```python
from vastai_sdk import VastAI  # equivalent to: from vastai import VastAI
```

## VastAI Class (High-Level SDK)

```python
from vastai import VastAI
vast = VastAI(api_key=None, server_url=None, retry=3, raw=False, quiet=False)
```

### Instance Management

```python
# List all your instances
instances = vast.show_instances()

# Get a single instance
instance = vast.show_instance(id=12345)

# Search GPU offers
offers = vast.search_offers(query='gpu_name=RTX_4090 num_gpus>=4 reliability>0.99')

# Create an instance from an offer
result = vast.create_instance(id=<offer_id>, image="pytorch/pytorch:latest", disk=50)

# Lifecycle
vast.start_instance(id=12345)
vast.stop_instance(id=12345)
vast.reboot_instance(id=12345)
vast.destroy_instance(id=12345)

# Label an instance
vast.label_instance(id=12345, label="my-training-run")

# Get SSH connection string
ssh_url = vast.ssh_url(id=12345)   # returns "ssh -p PORT user@host"
scp_url = vast.scp_url(id=12345)   # returns scp-compatible URL
```

### Search

```python
# Search GPU offers (use help(vast.search_offers) for full query syntax)
offers = vast.search_offers(query='gpu_name=RTX_3090 num_gpus>=2')

# Search volume offers
volumes = vast.search_volumes(query='...')

# Search network volumes
net_vols = vast.search_network_volumes()

# Search templates
templates = vast.search_templates()

# Search invoices
invoices = vast.search_invoices()
```

### Serverless Deployments

```python
# List all deployments
deployments = vast.show_deployments()

# Get a deployment
deployment = vast.show_deployment(id=42)

# Delete a deployment
vast.delete_deployment(id=42)
```

### Machine Management (Hosting)

```python
machines = vast.show_machines()
machine = vast.show_machine(id=10)
vast.list_machine(id=10, price_gpu=0.30)
vast.unlist_machine(id=10)
```

### SSH Keys

```python
keys = vast.show_ssh_keys()
vast.create_ssh_key(ssh_key="ssh-rsa AAAA...")
vast.delete_ssh_key(id=5)
```

### Team Management

```python
members = vast.show_members()
vast.invite_member(email="user@example.com", role="developer")
vast.remove_member(id=7)
```

## SyncClient (Low-Level Sync)

`SyncClient` provides typed, synchronous access to GPU offers and instances.

```python
from vastai import SyncClient

client = SyncClient(api_key="YOUR_API_KEY")  # or reads ~/.vast_api_key

# Search offers with structured filters
offers = client.search(
    num_gpus=2,
    gpu_name="RTX_4090",
    min_reliability=0.99,
    max_dph_total=2.0,
)

# Create an instance
instance = client.create_instance(
    offer_id=<id>,
    image="pytorch/pytorch:latest",
    disk_gb=50,
)

# List your instances
instances = client.show_instances()  # returns list[SyncInstance]

# Destroy an instance
client.destroy_instance(instance_or_id=12345)
```

## AsyncClient (Low-Level Async)

`AsyncClient` provides async access to GPU offers and instances. Use as an async context manager.

```python
import asyncio
from vastai import AsyncClient

async def main():
    async with AsyncClient(api_key="YOUR_API_KEY") as client:
        # Search offers
        offers = await client.search(num_gpus=1, gpu_name="A100")

        # Create instance
        instance = await client.create_instance(offer_id=<id>, image="ubuntu:22.04")

        # List instances
        instances = await client.show_instances()  # returns list[AsyncInstance]

        # Destroy instance
        await client.destroy_instance(instance_or_id=instance.id)

asyncio.run(main())
```

## Serverless Client

For inference endpoints (requires `pip install "vastai[serverless]"`):

```python
import asyncio
from vastai import Serverless

async def main():
    serverless = Serverless()  # reads ~/.vast_api_key

    # Get an endpoint
    endpoint = await serverless.get_endpoint("my-endpoint")

    # Make a request
    response = await serverless.request("/v1/completions", {
        "model": "Qwen/Qwen3-8B",
        "prompt": "Who are you?",
        "max_tokens": 100,
        "temperature": 0.7,
    })

    text = response["response"]["choices"][0]["text"]
    print(text)

asyncio.run(main())
```

## Common Patterns

```python
# Find cheapest 4x RTX 4090 and launch a job
from vastai import VastAI
vast = VastAI()

offers = vast.search_offers(query='gpu_name=RTX_4090 num_gpus=4 reliability>0.99')
cheapest = min(offers, key=lambda o: o['dph_total'])
result = vast.create_instance(id=cheapest['id'], image="pytorch/pytorch:latest", disk=100)
print(f"Launched instance: {result['new_contract']}")

# Use help() to explore method signatures
help(vast.search_offers)
help(vast.create_instance)
```

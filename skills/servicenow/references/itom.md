# ITOM (IT Operations Management)

## Discovery

### What Discovery Does
Finds devices, applications, and services on your network and populates the CMDB automatically.

### Discovery Schedules
```
Navigate: Discovery > Discovery Schedules

Key fields:
  - Name, Discover: CI type (Servers, Network, Cloud, etc.)
  - IP ranges / CIDR blocks
  - MID Server: which MID runs the discovery
  - Schedule: frequency (daily, weekly)
  - Max run time: prevent runaway scans
  
Types:
  - IP-based: scan IP ranges for devices
  - Cloud-based: AWS, Azure, GCP discovery
  - Kubernetes: container/cluster discovery
```

### MID Server
```
The MID (Management, Instrumentation, and Discovery) Server is a 
Java application installed on-premise that:
  - Runs Discovery probes against your network
  - Executes Orchestration activities
  - Handles IntegrationHub connections to internal systems
  
Setup:
  1. Download MID Server package from instance
  2. Install on a server with network access to targets
  3. Configure config.xml (instance URL, credentials)
  4. Validate from instance: MID Server > Servers
  
Key tables:
  - ecc_agent: MID Server records
  - ecc_queue: Input/output queue for MID communication
```

### Discovery Patterns (Horizontal)
```
Navigate: Pattern Designer

Patterns define HOW to discover specific application types.

Structure:
  - Trigger: entry point (e.g., listening port 3306 = MySQL)
  - Steps: commands to run (SSH, WMI, SNMP)
  - Parsing: extract data from command output
  - CI Creation: map parsed data to CMDB tables

Example — MySQL Pattern:
  1. Trigger: Port 3306 open
  2. SSH: `mysql --version`
  3. SSH: `mysql -e "SHOW DATABASES"`
  4. Parse: version, database names
  5. Create: cmdb_ci_db_mysql_instance + relationships
```

### Credentials
```
Navigate: Discovery > Credentials

Types:
  - SSH (Linux/Unix)
  - Windows (WMI/PowerShell)
  - SNMP (v1/v2c/v3)
  - VMware (vCenter)
  - Cloud (AWS/Azure/GCP API keys)
  
Security:
  - Credentials stored encrypted
  - Tag-based: assign credentials to IP ranges
  - Least privilege: discovery accounts need read-only access
```

## Event Management

### Event Collection
```
Sources:
  - SNMP traps → MID Server → Event table
  - Syslog → MID Server → Event table
  - REST API push → /api/global/em/jsonv2
  - Email parsing
  - Cloud monitoring (CloudWatch, Azure Monitor)
  - APM tools (Dynatrace, AppDynamics, Datadog)

Event table: em_event
Key fields:
  - Source, Node, Type, Resource
  - Severity (1-5: Critical to Clear)
  - Message key (deduplication identifier)
  - Additional info (JSON payload)
```

### Event Rules
```
Navigate: Event Management > Rules

Processing pipeline:
  1. Filtering rules — drop noise events
  2. Transform rules — normalize fields
  3. Deduplication — merge duplicate events
  4. Alert rules — create alerts from events
  
Deduplication:
  - Message key = unique identifier
  - Same message key = same event, update count
  - Prevents alert storms from flapping devices
```

### Alerts
```
Table: em_alert
Created from events after processing pipeline

Alert lifecycle:
  Open → Acknowledged → Reopen → Closed
  
Alert actions:
  - Create incident automatically
  - Run remediation flow
  - Notify on-call team
  - Execute Orchestration runbook
  
Alert Management Rules:
  Navigate: Event Management > Alert Management Rules
  - Secondary alerts: group related alerts
  - Alert correlation: link alerts to CIs
  - Maintenance windows: suppress during planned outages
```

### Operator Workspace
```
Event Management Operator Workspace:
  - Real-time alert dashboard
  - Service health map
  - Alert timeline
  - Contextual CMDB data
  
Configuration:
  Navigate: Event Management > Operator Workspace
```

## Service Mapping

### What Service Mapping Does
Discovers and maps **application services** — the relationships between servers, databases, load balancers, and other CIs that make up a business service.

### Service Map Creation
```
Navigate: Service Mapping > Home

Approaches:
  1. Top-Down Discovery
     - Start from entry point (URL, IP:port)
     - Discovery follows connections automatically
     - Maps entire service topology
     
  2. Traffic-Based Discovery
     - Analyze network traffic patterns
     - Build maps from actual communication flows
     
  3. Tag-Based (Cloud)
     - Use cloud resource tags to group CIs
     - AWS/Azure/GCP tagging conventions
```

### Service Mapping Patterns
```
Navigate: Service Mapping > Patterns

Connection patterns define how to follow relationships:
  - TCP connections between hosts
  - Load balancer → pool members
  - Application → database connections
  - Process → filesystem dependencies
  
Custom patterns for proprietary applications:
  - SSH: check config files for connection strings
  - API: query app health endpoints
  - File: parse config for upstream/downstream
```

### Business Service Maps
```
Table: cmdb_ci_service (Business Service)

Map displays:
  - Entry point (URL or IP)
  - Web servers
  - Application servers
  - Databases
  - Load balancers
  - Cloud resources
  - Relationships between all CIs

Used for:
  - Impact analysis (which services affected by this CI?)
  - Change risk assessment
  - Incident correlation
  - Capacity planning
```

## Orchestration

### Orchestration Activities
```
Navigate: Orchestration > Activities

Built-in activities:
  - SSH Command (Linux)
  - PowerShell (Windows)
  - REST Message
  - JDBC Query
  - SNMP Set
  - Cloud management (AWS EC2, Azure VM)
  
Custom activities:
  - Create via Activity Designer
  - Package as reusable components
  - Can be used in Flows and Playbooks
```

### Runbook Automation
```
Use case: Automated remediation

Example — Disk Space Alert:
  1. Alert fires: disk > 90% on server
  2. Alert rule triggers Flow
  3. Flow → SSH to server → Run cleanup script
  4. Check result → disk < 80%?
  5. Yes → Auto-close alert
  6. No → Create incident, page on-call
  
Implementation:
  - Flow trigger: Alert created, severity = Critical
  - Conditions: type = "disk_space"
  - Actions: SSH command via MID Server
  - Error handling: create incident if remediation fails
```

## Cloud Management

### Cloud Discovery
```
Supported clouds:
  - AWS (EC2, RDS, S3, Lambda, ELB, VPC)
  - Azure (VMs, SQL, Storage, Functions, App Service)
  - GCP (Compute, Cloud SQL, Storage, Functions)

Configuration:
  1. Cloud credentials (access keys or service principal)
  2. Discovery schedule targeting cloud provider
  3. Cloud regions to scan
  4. CI mapping rules (cloud resource → CMDB class)
```

### Cloud Provisioning
```
Navigate: Cloud Management > Cloud Services Catalog

Catalog items for cloud resources:
  - Provision VM (size, image, network)
  - Create database instance
  - Deploy container cluster
  
Lifecycle management:
  - Start/Stop/Restart
  - Resize/Scale
  - Snapshot/Backup
  - Decommission
```

## Health Log Analytics (HLA)

### Log Collection
```
Sources:
  - Application logs via MID Server
  - Cloud logs (CloudWatch Logs, Azure Log Analytics)
  - Container logs (stdout/stderr)
  
Processing:
  - Log sources → MID Server → HLA pipeline
  - Pattern detection: identify anomalies
  - Alert creation: unusual log patterns → alerts
  - Correlation: link log anomalies to CIs
```

## ITOM Best Practices

1. **Start with Discovery** — clean CMDB is foundation for everything
2. **Service Mapping after Discovery** — need CIs before mapping relationships
3. **Deduplicate aggressively** — event storms kill alert value
4. **Automate remediation** — common issues should self-heal
5. **Maintenance windows** — suppress during planned changes
6. **MID Server sizing** — dedicated MID per function (discovery, orchestration, events)
7. **Credential management** — rotate regularly, audit access
8. **Tag your cloud resources** — enables clean discovery and cost tracking
9. **Monitor MID Server health** — it's a SPOF for ITOM operations
10. **Start small** — discover one data center, then expand

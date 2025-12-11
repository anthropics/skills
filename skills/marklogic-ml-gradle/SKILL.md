---
name: marklogic-ml-gradle
description: >
  ml-gradle plugin for MarkLogic application development: deploy applications, manage modules,
  load data, update database indexes, run unit tests, and automate workflows. Covers project
  setup, module loading, data movement, configuration management, and multi-environment deployments.
---

# MarkLogic ml-gradle Plugin

Automate MarkLogic application lifecycle with ml-gradle: setup projects, deploy configurations, load modules (XQuery/JavaScript/XSLT), manage data, update indexes, and run unit tests across multiple environments.

## When to Use This Skill

Apply this skill when tasks involve:
- Setting up new MarkLogic application projects
- Deploying MarkLogic applications to dev/test/prod environments
- Loading and reloading modules (XQuery, JavaScript, XSLT)
- Updating database indexes without full redeployment
- Loading data (documents, triples, CSV/JSON/XML)
- Running MarkLogic unit tests
- Managing multi-environment configurations
- Automating MarkLogic workflows in CI/CD pipelines

## Overview

**ml-gradle** is a Gradle plugin that manages the complete MarkLogic application lifecycle through Gradle tasks. It uses MarkLogic's Manage and Admin APIs to deploy resources and load modules.

**Key Capabilities:**
- ✅ Deploy databases, app servers, security (users/roles), triggers
- ✅ Load application modules into modules database
- ✅ Update database indexes incrementally
- ✅ Bulk load data from files
- ✅ Run XQuery/JavaScript unit tests
- ✅ Export/import data for migrations
- ✅ Multi-environment configuration management

## Installation

### Prerequisites

- **MarkLogic Server** installed and running
- **Java 8+** installed
- **Gradle 6+** installed (or use Gradle wrapper)

### Create New ml-gradle Project

```bash
# Generate new ml-gradle project
gradle mlNewProject

# Or specify project name
gradle -PprojectName=my-app mlNewProject
```

This creates:
```
my-app/
├── build.gradle           # Gradle build configuration
├── gradle.properties      # MarkLogic connection settings
└── src/main/
    ├── ml-config/        # Database/server configs
    └── ml-modules/       # Application modules
```

### Add ml-gradle to Existing Project

Edit `build.gradle`:

```gradle
plugins {
  id "com.marklogic.ml-gradle" version "4.6.0"
}

repositories {
  mavenCentral()
  maven { url "https://developer.marklogic.com/maven2/" }
}
```

## Project Layout

### Standard Directory Structure

```
project-root/
├── build.gradle                # Gradle configuration
├── gradle.properties           # Default environment config
├── gradle-dev.properties       # Dev-specific overrides
├── gradle-local.properties     # Local developer overrides (gitignore)
├── gradle-test.properties      # Test environment
├── gradle-prod.properties      # Production environment
│
└── src/main/
    ├── ml-config/              # MarkLogic resource configs
    │   ├── rest-api.json       # REST API configuration
    │   ├── databases/          # Database configs
    │   │   ├── content-database.json
    │   │   ├── modules-database.json
    │   │   └── content-database/  # Database-specific resources
    │   │       ├── alerts/
    │   │       ├── triggers/
    │   │       └── temporal/
    │   ├── servers/            # App server configs
    │   │   └── rest-server.json
    │   └── security/           # Security configs
    │       ├── users/
    │       ├── roles/
    │       ├── amps/
    │       └── privileges/
    │
    ├── ml-modules/             # Application modules
    │   ├── root/               # Root modules (/)
    │   │   ├── lib/
    │   │   └── custom/
    │   ├── services/           # REST services
    │   ├── transforms/         # REST transforms
    │   ├── options/            # Search options
    │   └── ext/                # Extensions
    │
    ├── ml-schemas/             # Schema files (.xsd, .tdex, etc.)
    ├── ml-data/                # Data files to load
    └── ml-plugins/             # System plugins

└── src/test/
    └── ml-modules/             # Unit test modules
        └── root/test/
            ├── suites/
            └── test-*.xqy
```

## Essential Configuration

### gradle.properties

```properties
# MarkLogic Connection
mlHost=localhost
mlUsername=admin
mlPassword=admin

# Ports
mlAppServicesPort=8000
mlAdminPort=8001
mlManagePort=8002
mlRestPort=8003
mlTestRestPort=8004

# Application
mlAppName=my-app
mlModulesDatabaseName=my-app-modules
mlContentDatabaseName=my-app-content

# Deployment
mlModulePaths=src/main/ml-modules
mlConfigPath=src/main/ml-config
```

### Port Reference

| Port | Property | Purpose |
|------|----------|---------|
| 8000 | `mlAppServicesPort` | App-Services server for loading modules |
| 8001 | `mlAdminPort` | Admin server for management APIs |
| 8002 | `mlManagePort` | Manage server for deploying resources |
| Custom | `mlRestPort` | Application-specific REST server |
| Custom | `mlTestRestPort` | Optional test REST environment |

## Essential Workflows

### Workflow 1: Initial Project Setup

**Phase 1: Create and configure project**
```bash
# Create new project
gradle mlNewProject

# Edit gradle.properties with your environment settings
# mlHost, mlUsername, mlPassword, mlRestPort

# Review and customize configs in src/main/ml-config/
```

**Phase 2: Deploy application**
```bash
# Deploy everything: databases, servers, security, modules
gradle mlDeploy

# Or deploy incrementally
gradle mlDeployApp      # Deploy databases and servers only
gradle mlLoadModules    # Load modules only
```

**Expected timing:**
- Initial `mlDeploy`: 30-120 seconds (depends on resources)
- Incremental `mlLoadModules`: 5-15 seconds

### Workflow 2: Development Loop (Module Changes)

**Phase 1: Edit modules**
```bash
# Edit files in src/main/ml-modules/
# Example: src/main/ml-modules/root/lib/util.xqy
```

**Phase 2: Reload modules (fast feedback)**
```bash
# Option 1: Manual reload (recommended for quick changes)
gradle mlLoadModules

# Option 2: Watch mode (auto-reload on file changes)
gradle mlWatch -i

# Option 3: Reload specific module
gradle mlLoadModules -PmodulePath=src/main/ml-modules/root/lib/util.xqy
```

**Phase 3: Test changes**
```bash
# Run unit tests
gradle mlUnitTest

# Or test manually in Query Console (http://localhost:8000/qconsole)
```

**Expected timing:**
- `mlLoadModules`: 5-15 seconds
- `mlWatch` (initial): 10 seconds, then instant reloads
- `mlUnitTest`: 10-30 seconds (depends on test count)

**When to run:**
- **During development:** `mlWatch` for automatic reloads
- **Before committing:** `mlUnitTest` to verify tests pass
- **After major changes:** Full `mlDeploy` if configs changed

### Workflow 3: Database Configuration Updates

**Phase 1: Update database configuration**
```bash
# Edit src/main/ml-config/databases/content-database.json
# Add range indexes, lexicons, geospatial indexes, etc.
```

**Phase 2: Apply index updates**
```bash
# Update indexes without full redeploy (faster)
gradle mlUpdateIndexes

# Or full redeploy (slower, but ensures consistency)
gradle mlDeploy
```

**Phase 3: Verify indexes**
```bash
# Check in Admin UI (http://localhost:8001)
# Or query via Query Console
```

**Expected timing:**
- `mlUpdateIndexes`: 10-30 seconds (depends on index count)
- Full `mlDeploy`: 30-120 seconds

**When to use mlUpdateIndexes:**
- ✅ Adding new range indexes
- ✅ Modifying existing indexes
- ✅ Adding geospatial or lexical indexes
- ❌ Changing database structure (use `mlDeploy`)

### Workflow 4: Data Loading

**Phase 1: Prepare data files**
```bash
# Place files in src/main/ml-data/ or data/
# Supports JSON, XML, CSV, text files

data/
├── documents/
│   ├── doc1.json
│   └── doc2.xml
└── csv/
    └── products.csv
```

**Phase 2: Load data**
```bash
# Load all data from configured directory
gradle mlLoadData

# Or specify custom data directory
gradle mlLoadData -PdataDir=data/import

# For large datasets, use batch loading
gradle mlImportAndFinish -PdataDir=data/bulk
```

**Expected timing:**
- Small datasets (< 1000 docs): 5-15 seconds
- Medium datasets (1000-10000 docs): 30-120 seconds
- Large datasets (> 10000 docs): Use Data Movement tasks

### Workflow 5: Multi-Environment Deployment

**Phase 1: Configure environments**
```bash
# gradle.properties (defaults)
mlHost=localhost
mlRestPort=8003

# gradle-dev.properties
mlHost=dev-server.example.com
mlRestPort=8010

# gradle-test.properties
mlHost=test-server.example.com
mlRestPort=9010

# gradle-prod.properties
mlHost=prod-server.example.com
mlRestPort=10010
```

**Phase 2: Deploy to specific environment**
```bash
# Deploy to dev
gradle mlDeploy -PenvironmentName=dev

# Deploy to test
gradle mlDeploy -PenvironmentName=test

# Deploy to prod
gradle mlDeploy -PenvironmentName=prod
```

**Phase 3: Verify deployment**
```bash
# Check REST endpoint
curl http://test-server.example.com:9010/v1/ping

# Run smoke tests
gradle mlUnitTest -PenvironmentName=test
```

**Expected timing:**
- Deploy to dev: 30-60 seconds
- Deploy to test/prod: 60-120 seconds (more validation)

**Pipeline example:**
```bash
# CI/CD pipeline stages
# Stage 1: Deploy to dev automatically
gradle mlDeploy -PenvironmentName=dev

# Stage 2: Run tests on dev
gradle mlUnitTest -PenvironmentName=dev

# Stage 3: Deploy to test (manual approval)
gradle mlDeploy -PenvironmentName=test

# Stage 4: Deploy to prod (manual approval)
gradle mlDeploy -PenvironmentName=prod
```

## Core Gradle Tasks

### Deploy Tasks

| Task | Purpose | When to Use |
|------|---------|-------------|
| `mlDeploy` | Deploy all resources (databases, servers, security, modules) | Initial setup, full deployment |
| `mlRedeploy` | Undeploy then deploy (fresh start) | Reset environment, clean slate |
| `mlUndeploy` | Remove all deployed resources | Teardown, cleanup |
| `mlDeployApp` | Deploy databases and servers only | Skip modules/security |
| `mlLoadModules` | Load modules only | Module changes during development |
| `mlReloadModules` | Clear modules database then reload | Fix module loading issues |
| `mlWatch` | Auto-reload modules on file changes | Active development |

### Data Tasks

| Task | Purpose | When to Use |
|------|---------|-------------|
| `mlLoadData` | Load data from ml-data directory | Initial data setup |
| `mlImportAndFinish` | Bulk import with Data Movement SDK | Large datasets |
| `mlExport` | Export data to files | Backup, migration |
| `mlExportModules` | Export modules to files | Backup modules |
| `mlExportSchemas` | Export schemas to files | Backup schemas |

### Database Tasks

| Task | Purpose | When to Use |
|------|---------|-------------|
| `mlUpdateIndexes` | Update database indexes | Add/modify indexes without full redeploy |

### Modules Tasks

| Task | Purpose | When to Use |
|------|---------|-------------|
| `mlLoadModules` | Load modules from ml-modules directory | Module updates |
| `mlReloadModules` | Clear and reload all modules | Fix module issues |
| `mlWatch` | Watch for file changes and auto-reload | Development loop |

### Unit Test Tasks

| Task | Purpose | When to Use |
|------|---------|-------------|
| `mlUnitTest` | Run all unit tests | Verify code works |
| `mlUnitTestTestSuite` | Run specific test suite | Test specific module |

**Test parameters:**
```bash
# Run specific test module
gradle mlUnitTest -PunitTestModule=/test/my-test.xqy

# Run specific test suite
gradle mlUnitTest -PunitTestSuite=MySuite
```

## How Modules Are Loaded

**Module Loading Strategy:**

1. **Load to Modules Database:** Modules are stored in the modules database (default: `{appName}-modules`)
2. **URI Mapping:** File paths map to URIs in the database
   - `src/main/ml-modules/root/lib/util.xqy` → `/lib/util.xqy`
   - `src/main/ml-modules/services/search.xqy` → `/services/search.xqy`

3. **REST-Specific Modules:** Some modules require REST server:
   - `services/` → REST services
   - `transforms/` → REST transforms
   - `options/` → Search options

**Module Load Ports:**
- Non-REST modules: Use `mlAppServicesPort` (default 8000)
- REST modules: Use `mlRestPort` (your app's REST server)

**Watch Mode:**
```bash
# Start watch mode (monitors file changes)
gradle mlWatch

# Now edit files - they auto-reload
# Stop with Ctrl+C
```

## Common Patterns

### Pattern 1: New MarkLogic Application

```bash
# Step 1: Create project
gradle mlNewProject -PprojectName=my-app
cd my-app

# Step 2: Configure
# Edit gradle.properties:
#   mlHost=localhost
#   mlRestPort=8003
#   mlAppName=my-app

# Step 3: Deploy
gradle mlDeploy

# Step 4: Verify
curl http://localhost:8003/v1/ping
```

### Pattern 2: Add Range Index

```bash
# Step 1: Edit database config
# src/main/ml-config/databases/content-database.json
{
  "database-name": "my-app-content",
  "range-element-index": [
    {
      "scalar-type": "string",
      "namespace-uri": "",
      "localname": "email",
      "collation": "http://marklogic.com/collation/"
    }
  ]
}

# Step 2: Update indexes
gradle mlUpdateIndexes

# Step 3: Verify in Admin UI or Query Console
```

### Pattern 3: Module Development Loop

```bash
# Terminal 1: Start watch mode
gradle mlWatch

# Terminal 2: Edit modules
vim src/main/ml-modules/root/lib/my-lib.xqy

# Watch mode automatically reloads on save

# Terminal 2: Run tests
gradle mlUnitTest
```

### Pattern 4: Load Data from CSV

```bash
# Step 1: Place CSV in data directory
# data/products.csv

# Step 2: Create MLCP options (optional)
# src/main/ml-config/mlcp-options.txt
# -mode local
# -document_type json
# -transform_module /transforms/csv-to-json.xqy

# Step 3: Load data
gradle mlLoadData -PdataDir=data

# Or with MLCP
gradle mlImportAndFinish -PdataDir=data -Pmlcp.input_file_path=products.csv
```

### Pattern 5: Run Unit Tests

```bash
# Create test module
# src/test/ml-modules/root/test/test-util.xqy
xquery version "1.0-ml";

import module namespace test = "http://marklogic.com/test"
  at "/test/test-helper.xqy";

test:assert-equal("hello", fn:lower-case("HELLO"))

# Run all tests
gradle mlUnitTest

# Run specific test
gradle mlUnitTest -PunitTestModule=/test/test-util.xqy

# See results in terminal or test-results/
```

### Pattern 6: Export Data for Backup

```bash
# Export all data
gradle mlExport -PexportDir=backup/$(date +%Y%m%d)

# Export modules
gradle mlExportModules -PexportDir=backup/modules

# Export specific collection
gradle mlExport -PexportDir=backup -Pcollections=products
```

## Configuration Management

### Environment-Specific Properties

**Strategy:** Create property files per environment

```bash
# gradle.properties (defaults for local dev)
mlHost=localhost
mlUsername=admin
mlPassword=admin
mlRestPort=8003

# gradle-dev.properties (dev server)
mlHost=dev.example.com
mlRestPort=8010

# gradle-test.properties (test server)
mlHost=test.example.com
mlRestPort=9010

# gradle-prod.properties (production)
mlHost=prod.example.com
mlRestPort=10010
```

**Usage:**
```bash
# Use default (local)
gradle mlDeploy

# Use dev
gradle mlDeploy -PenvironmentName=dev

# Use test
gradle mlDeploy -PenvironmentName=test
```

### Secure Credentials

**Option 1: Environment variables**
```bash
# gradle.properties
mlUsername=${env.ML_USERNAME}
mlPassword=${env.ML_PASSWORD}

# Set in shell
export ML_USERNAME=admin
export ML_PASSWORD=secret

gradle mlDeploy
```

**Option 2: Command-line override**
```bash
gradle mlDeploy -PmlUsername=admin -PmlPassword=secret
```

**Option 3: gradle-local.properties (gitignored)**
```bash
# .gitignore
gradle-local.properties

# gradle-local.properties (not committed)
mlUsername=admin
mlPassword=secret
```

## Bundled Resources

### Scripts (`scripts/`)

**`new-project.sh`** - Create new ml-gradle project with boilerplate
```bash
./scripts/new-project.sh my-app
```

**`deploy-all-envs.sh`** - Deploy to multiple environments
```bash
./scripts/deploy-all-envs.sh
```

**`backup-data.sh`** - Export data with timestamp
```bash
./scripts/backup-data.sh
```

### Example Configs (`assets/`)

- `gradle.properties` - Complete example configuration
- `build.gradle` - Sample build file with ml-gradle plugin
- `content-database.json` - Example database configuration with indexes
- `rest-server.json` - Example REST server configuration
- `role-example.json` - Example security role
- `user-example.json` - Example security user

### Detailed Reference (`references/`)

- `TASK_REFERENCE.md` - Complete list of all ml-gradle tasks
- `MODULE_LOADING.md` - Deep dive on how modules are loaded
- `DATA_MOVEMENT.md` - Guide to data loading and export tasks

## Best Practices

**Project Organization:**
- Use standard ml-gradle directory structure
- Separate configs by environment (gradle-{env}.properties)
- Gitignore gradle-local.properties for local credentials
- Organize modules by type (lib/, custom/, util/)

**Development Workflow:**
- Use `mlWatch` during active development
- Run `mlUnitTest` before committing changes
- Use `mlLoadModules` for quick module updates
- Use `mlUpdateIndexes` instead of full `mlDeploy` when only indexes change

**Deployment:**
- Deploy to dev automatically in CI/CD
- Require approval for test/prod deployments
- Run tests after every deployment
- Use environment-specific property files

**Security:**
- Never commit passwords in gradle.properties
- Use environment variables or gradle-local.properties
- Create least-privilege roles and users
- Use SSL in production (mlManageSimpleSsl=true)

**Testing:**
- Write unit tests for all custom modules
- Run tests in CI/CD pipeline
- Use test REST server (mlTestRestPort) for isolation
- Test data loading workflows

## Troubleshooting

**Module loading fails:**
```bash
# Check credentials
gradle mlDeploy -PmlUsername=admin -PmlPassword=admin

# Clear and reload
gradle mlReloadModules

# Verify modules database exists
# Check Admin UI → Databases → {app}-modules
```

**Port conflicts:**
```bash
# Error: Port 8003 already in use

# Solution 1: Change port in gradle.properties
mlRestPort=8004

# Solution 2: Stop conflicting service
# Check what's using port: lsof -i :8003
```

**Deployment errors:**
```bash
# Error: Cannot connect to Manage server

# Check MarkLogic is running
curl http://localhost:8002/manage/v2

# Verify credentials
gradle mlDeploy -PmlUsername=admin -PmlPassword=correct-password

# Check user has manage-admin role
```

**Index updates not working:**
```bash
# Ensure you edited the right database config
# src/main/ml-config/databases/{database-name}.json

# Run with verbose logging
gradle mlUpdateIndexes --info

# Or do full redeploy
gradle mlDeploy
```

**Unit tests fail:**
```bash
# Check test module paths
# Should be in src/test/ml-modules/root/test/

# Verify test framework loaded
gradle mlLoadModules

# Run with verbose output
gradle mlUnitTest --info

# Check test-results/ for details
cat test-results/*.xml
```

## Integration with CI/CD

### GitHub Actions Example

```yaml
name: Deploy MarkLogic App

on:
  push:
    branches: [main, develop]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Set up Java
        uses: actions/setup-java@v3
        with:
          java-version: '11'
          distribution: 'adopt'

      - name: Deploy to dev
        run: |
          gradle mlDeploy \
            -PenvironmentName=dev \
            -PmlUsername=${{ secrets.ML_USERNAME }} \
            -PmlPassword=${{ secrets.ML_PASSWORD }}

      - name: Run unit tests
        run: |
          gradle mlUnitTest \
            -PenvironmentName=dev \
            -PmlUsername=${{ secrets.ML_USERNAME }} \
            -PmlPassword=${{ secrets.ML_PASSWORD }}
```

## Quality Integration

For MarkLogic XQuery/JavaScript code quality:
- Use **MarkLogic Unit Test Framework** for testing
- Use **XQuery linters** for code quality
- See **xquery-stdlib** skill for XQuery standard functions

This skill focuses on ml-gradle tooling and deployment workflows.

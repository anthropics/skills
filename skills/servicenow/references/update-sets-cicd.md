# Update Sets & CI/CD

## Update Sets

### What Are Update Sets?
Update Sets capture **configuration changes** (not data) made in an instance. They're the primary mechanism for moving customizations between instances (Dev → Test → Prod).

### Tracked vs Untracked Changes
```
Tracked (captured in update sets):
  ✅ Business Rules, Client Scripts, Script Includes
  ✅ UI Policies, UI Actions
  ✅ ACLs, Roles
  ✅ Forms, Lists, Related Lists
  ✅ Flows, Subflows
  ✅ Catalog Items, Variables
  ✅ System Properties
  ✅ Scheduled Jobs (definition)
  ✅ Notifications
  ✅ Application Files (scoped apps)

NOT tracked:
  ❌ Data records (incidents, users, etc.)
  ❌ Attachments (unless on tracked records)
  ❌ Homepages/dashboards (user-specific)
  ❌ Update Set records themselves
  ❌ Import Sets, Transform Maps (usually)
```

### Creating & Managing Update Sets
```
Navigate: System Update Sets > Local Update Sets

Best practices:
  - One update set per feature/story
  - Naming: "STRY0012345 - Add VIP flag to incident form"
  - Never work in "Default" update set
  - Close update set when feature is complete
  - Review contents before promoting
```

### Retrieving Update Sets (Target Instance)
```
Navigate: System Update Sets > Retrieved Update Sets

Steps:
  1. Source instance: Complete and close update set
  2. Target instance: Navigate to Retrieved Update Sets
  3. Click "Retrieve Update Sets" → select source
  4. Preview (check for conflicts)
  5. Resolve conflicts (if any)
  6. Commit

Conflict types:
  - Record exists in target with different update set
  - Record deleted in target but modified in source
  - Collision: same record modified in both

Resolution options:
  - Accept remote (source wins)
  - Accept local (target wins)
  - Manual merge
```

### Batch Update Sets
```
Use case: Group related update sets for a single deployment

Creating:
  1. Create Batch parent record
  2. Add child update sets (in commit order)
  3. Preview and commit the batch

Benefits:
  - Atomic deployment (all or nothing)
  - Controlled commit order
  - Single preview/commit action
```

### Update Set Best Practices
```
1. One feature per update set — easy rollback
2. Never put data fixes in update sets — use Fix Scripts
3. Close update sets promptly — avoid capturing unintended changes
4. Preview before commit — always
5. Back out plan — know how to revert each update set
6. Don't modify OOB records when possible — use insert/override
7. Test in sub-prod first — never commit directly to Prod
8. Document the update set — description field exists, use it
```

## Source Control Integration

### Git Integration (App Repository)
```
Navigate: System Applications > Studio > Source Control

Setup:
  1. Create Git repo (GitHub, GitLab, Bitbucket, Azure DevOps)
  2. Generate credentials (SSH key or token)
  3. In Studio: Source Control > Link to Source Control
  4. Configure: URL, branch, credentials
  
Operations:
  - Commit: Push app files to Git
  - Apply Remote Changes: Pull from Git
  - Stash: Temporary save (like git stash)
  - Create Branch: Feature branching
  - Switch Branch: Change active branch
```

### App Repository Structure in Git
```
my-scoped-app/
├── README.md
├── sn_source_control.properties
├── checksum.json
├── sys_app_<sys_id>.xml              # App record
├── sys_script_include/                # Script Includes
│   ├── MyUtils_<sys_id>.xml
│   └── MyHelper_<sys_id>.xml
├── sys_script/                        # Business Rules
│   ├── ValidateIncident_<sys_id>.xml
│   └── AutoAssign_<sys_id>.xml
├── sys_ui_policy/                     # UI Policies
├── sys_client_script/                 # Client Scripts
├── sys_security_acl/                  # ACLs
├── sys_flow/                          # Flows
└── sys_hub_action/                    # Flow actions
```

## CI/CD with ServiceNow

### ServiceNow CI/CD API
```
Base URL: /api/sn_cicd/

Endpoints:
  POST /app/install          — Install app from source control
  POST /app/publish           — Publish app to app repo  
  POST /app/apply_changes     — Apply remote source control changes
  GET  /progress/{result_id}  — Check operation status
  POST /testsuite/run         — Run ATF test suite
  GET  /testsuite/results     — Get test results
  POST /app_repo/rollback     — Rollback app version
  POST /sc/apply_changes      — Apply source control changes
  POST /plugin/activate       — Activate a plugin
  POST /instance/scan         — Run instance scan
```

### GitHub Actions Pipeline
```yaml
# .github/workflows/servicenow-cicd.yml
name: ServiceNow CI/CD

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install App to Dev
        uses: ServiceNow/sncicd-install-app@v2
        with:
          instanceUrl: ${{ secrets.SN_DEV_URL }}
          appSysId: ${{ secrets.APP_SYS_ID }}
          scope: ${{ secrets.APP_SCOPE }}
        env:
          snowUsername: ${{ secrets.SN_USERNAME }}
          snowPassword: ${{ secrets.SN_PASSWORD }}
      
      - name: Run ATF Tests
        uses: ServiceNow/sncicd-tests-run@v2
        with:
          instanceUrl: ${{ secrets.SN_DEV_URL }}
          testSuiteSysId: ${{ secrets.TEST_SUITE_ID }}
        env:
          snowUsername: ${{ secrets.SN_USERNAME }}
          snowPassword: ${{ secrets.SN_PASSWORD }}
      
      - name: Publish App
        if: github.ref == 'refs/heads/main'
        uses: ServiceNow/sncicd-publish-app@v2
        with:
          instanceUrl: ${{ secrets.SN_DEV_URL }}
          appSysId: ${{ secrets.APP_SYS_ID }}
          versionFormat: autodetect
        env:
          snowUsername: ${{ secrets.SN_USERNAME }}
          snowPassword: ${{ secrets.SN_PASSWORD }}
      
      - name: Install to Prod
        if: github.ref == 'refs/heads/main'
        uses: ServiceNow/sncicd-install-app@v2
        with:
          instanceUrl: ${{ secrets.SN_PROD_URL }}
          appSysId: ${{ secrets.APP_SYS_ID }}
        env:
          snowUsername: ${{ secrets.SN_USERNAME }}
          snowPassword: ${{ secrets.SN_PASSWORD }}
```

### Azure DevOps Pipeline
```yaml
# azure-pipelines.yml
trigger:
  branches:
    include:
      - main

pool:
  vmImage: 'ubuntu-latest'

stages:
  - stage: Build
    jobs:
      - job: ApplyChanges
        steps:
          - task: ServiceNow-CICD-App-Apply-Changes@1
            inputs:
              connectedServiceName: 'ServiceNow-Dev'
              appScope: 'x_myco_myapp'
              branch: 'main'

  - stage: Test
    dependsOn: Build
    jobs:
      - job: RunATF
        steps:
          - task: ServiceNow-CICD-Run-Test-Suite@1
            inputs:
              connectedServiceName: 'ServiceNow-Dev'
              testSuiteSysId: '$(TEST_SUITE_ID)'
              
  - stage: Deploy
    dependsOn: Test
    condition: succeeded()
    jobs:
      - deployment: Production
        environment: 'production'
        strategy:
          runOnce:
            deploy:
              steps:
                - task: ServiceNow-CICD-App-Install@1
                  inputs:
                    connectedServiceName: 'ServiceNow-Prod'
                    appSysId: '$(APP_SYS_ID)'
```

### Jenkins Pipeline
```groovy
pipeline {
    agent any
    
    environment {
        SN_CREDS = credentials('servicenow-credentials')
        SN_DEV = 'https://dev12345.service-now.com'
        SN_PROD = 'https://prod12345.service-now.com'
        APP_SYS_ID = 'abc123...'
    }
    
    stages {
        stage('Apply Source Control') {
            steps {
                snApplyChanges(
                    url: "${SN_DEV}",
                    credentialsId: 'servicenow-credentials',
                    appScope: 'x_myco_myapp',
                    branch: 'main'
                )
            }
        }
        
        stage('Run Tests') {
            steps {
                snRunTestSuite(
                    url: "${SN_DEV}",
                    credentialsId: 'servicenow-credentials',
                    testSuiteSysId: env.TEST_SUITE_ID
                )
            }
        }
        
        stage('Deploy to Prod') {
            when { branch 'main' }
            steps {
                snInstallApp(
                    url: "${SN_PROD}",
                    credentialsId: 'servicenow-credentials',
                    appSysId: "${APP_SYS_ID}"
                )
            }
        }
    }
}
```

## Deployment Best Practices

1. **Dev → Test → Stage → Prod** — minimum 3 environments for enterprise
2. **Automated ATF** on every deployment — catch regressions early
3. **Instance Scan** before promoting — check for best practice violations
4. **Version your apps** semantically — major.minor.patch
5. **Never develop in Prod** — exception: emergency fix with immediate backport
6. **Branch strategy:** main = production, develop = current sprint, feature/* = individual stories
7. **Code review** via Git PRs — even for ServiceNow development
8. **Rollback plan** for every deployment — test rollback in sub-prod
9. **Freeze periods** — no deployments during critical business windows
10. **Change records** for every Prod deployment — automate creation via CI/CD

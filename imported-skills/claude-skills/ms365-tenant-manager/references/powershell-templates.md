# PowerShell Script Templates

Ready-to-use PowerShell scripts for Microsoft 365 administration with error handling and best practices.

---

## Table of Contents

- [Prerequisites](#prerequisites)
- [Security Audit Script](#security-audit-script)
- [Conditional Access Policy](#conditional-access-policy)
- [Bulk User Provisioning](#bulk-user-provisioning)
- [User Offboarding](#user-offboarding)
- [License Management](#license-management)
- [DNS Records Configuration](#dns-records-configuration)

---

## Prerequisites

Install required modules before running scripts:

```powershell
# Install Microsoft Graph module (recommended)
Install-Module Microsoft.Graph -Scope CurrentUser -Force

# Install Exchange Online module
Install-Module ExchangeOnlineManagement -Scope CurrentUser -Force

# Install Teams module
Install-Module MicrosoftTeams -Scope CurrentUser -Force

# Verify installations
Get-InstalledModule Microsoft.Graph, ExchangeOnlineManagement, MicrosoftTeams
```

---

## Security Audit Script

Comprehensive security audit for MFA status, admin accounts, inactive users, and permissions.

```powershell
<#
.SYNOPSIS
    Microsoft 365 Security Audit Report

.DESCRIPTION
    Performs comprehensive security audit and generates CSV reports.
    Checks: MFA status, admin accounts, inactive users, guest access, licenses

.OUTPUTS
    CSV reports in SecurityAudit_[timestamp] directory
#>

#Requires -Modules Microsoft.Graph, ExchangeOnlineManagement

param(
    [int]$InactiveDays = 90,
    [string]$OutputPath = "."
)

# Connect to services
Connect-MgGraph -Scopes "Directory.Read.All", "User.Read.All", "AuditLog.Read.All"
Connect-ExchangeOnline

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$reportPath = Join-Path $OutputPath "SecurityAudit_$timestamp"
New-Item -ItemType Directory -Path $reportPath -Force | Out-Null

Write-Host "Starting Security Audit..." -ForegroundColor Cyan

# 1. MFA Status Check
Write-Host "[1/5] Checking MFA status..." -ForegroundColor Yellow

$users = Get-MgUser -All -Property Id,DisplayName,UserPrincipalName,AccountEnabled
$mfaReport = @()

foreach ($user in $users) {
    $authMethods = Get-MgUserAuthenticationMethod -UserId $user.Id -ErrorAction SilentlyContinue
    $hasMFA = ($authMethods | Where-Object { $_.AdditionalProperties.'@odata.type' -ne '#microsoft.graph.passwordAuthenticationMethod' }).Count -gt 0

    $mfaReport += [PSCustomObject]@{
        UserPrincipalName = $user.UserPrincipalName
        DisplayName       = $user.DisplayName
        AccountEnabled    = $user.AccountEnabled
        MFAEnabled        = $hasMFA
        AuthMethodsCount  = $authMethods.Count
    }
}

$mfaReport | Export-Csv -Path "$reportPath/MFA_Status.csv" -NoTypeInformation
$usersWithoutMFA = ($mfaReport | Where-Object { -not $_.MFAEnabled -and $_.AccountEnabled }).Count
Write-Host "  Users without MFA: $usersWithoutMFA" -ForegroundColor $(if($usersWithoutMFA -gt 0){'Red'}else{'Green'})

# 2. Admin Roles Audit
Write-Host "[2/5] Auditing admin roles..." -ForegroundColor Yellow

$adminRoles = Get-MgDirectoryRole -All
$adminReport = @()

foreach ($role in $adminRoles) {
    $members = Get-MgDirectoryRoleMember -DirectoryRoleId $role.Id -All
    foreach ($member in $members) {
        $memberUser = Get-MgUser -UserId $member.Id -ErrorAction SilentlyContinue
        if ($memberUser) {
            $adminReport += [PSCustomObject]@{
                UserPrincipalName = $memberUser.UserPrincipalName
                DisplayName       = $memberUser.DisplayName
                Role              = $role.DisplayName
                AccountEnabled    = $memberUser.AccountEnabled
            }
        }
    }
}

$adminReport | Export-Csv -Path "$reportPath/Admin_Roles.csv" -NoTypeInformation
Write-Host "  Admin assignments: $($adminReport.Count)" -ForegroundColor Cyan

# 3. Inactive Users
Write-Host "[3/5] Finding inactive users ($InactiveDays+ days)..." -ForegroundColor Yellow

$inactiveDate = (Get-Date).AddDays(-$InactiveDays)
$inactiveUsers = Get-MgUser -All -Property Id,DisplayName,UserPrincipalName,SignInActivity,AccountEnabled |
    Where-Object {
        $_.AccountEnabled -and
        $_.SignInActivity.LastSignInDateTime -and
        $_.SignInActivity.LastSignInDateTime -lt $inactiveDate
    } |
    Select-Object UserPrincipalName, DisplayName,
        @{N='LastSignIn';E={$_.SignInActivity.LastSignInDateTime}},
        @{N='DaysSinceSignIn';E={((Get-Date) - $_.SignInActivity.LastSignInDateTime).Days}}

$inactiveUsers | Export-Csv -Path "$reportPath/Inactive_Users.csv" -NoTypeInformation
Write-Host "  Inactive users: $($inactiveUsers.Count)" -ForegroundColor $(if($inactiveUsers.Count -gt 0){'Yellow'}else{'Green'})

# 4. Guest Users
Write-Host "[4/5] Reviewing guest access..." -ForegroundColor Yellow

$guestUsers = Get-MgUser -Filter "userType eq 'Guest'" -All -Property UserPrincipalName,DisplayName,AccountEnabled,CreatedDateTime
$guestUsers | Select-Object UserPrincipalName, DisplayName, AccountEnabled, CreatedDateTime |
    Export-Csv -Path "$reportPath/Guest_Users.csv" -NoTypeInformation
Write-Host "  Guest users: $($guestUsers.Count)" -ForegroundColor Cyan

# 5. License Usage
Write-Host "[5/5] Analyzing licenses..." -ForegroundColor Yellow

$licenses = Get-MgSubscribedSku -All
$licenseReport = foreach ($lic in $licenses) {
    [PSCustomObject]@{
        ProductName       = $lic.SkuPartNumber
        TotalLicenses     = $lic.PrepaidUnits.Enabled
        AssignedLicenses  = $lic.ConsumedUnits
        AvailableLicenses = $lic.PrepaidUnits.Enabled - $lic.ConsumedUnits
        Utilization       = [math]::Round(($lic.ConsumedUnits / [math]::Max($lic.PrepaidUnits.Enabled, 1)) * 100, 1)
    }
}

$licenseReport | Export-Csv -Path "$reportPath/License_Usage.csv" -NoTypeInformation
Write-Host "  License SKUs: $($licenses.Count)" -ForegroundColor Cyan

# Summary
Write-Host "`n=== Security Audit Summary ===" -ForegroundColor Green
Write-Host "Total Users: $($users.Count)"
Write-Host "Users without MFA: $usersWithoutMFA $(if($usersWithoutMFA -gt 0){'[ACTION REQUIRED]'})"
Write-Host "Inactive Users: $($inactiveUsers.Count)"
Write-Host "Guest Users: $($guestUsers.Count)"
Write-Host "Admin Assignments: $($adminReport.Count)"
Write-Host "`nReports saved to: $reportPath" -ForegroundColor Green

# Disconnect
Disconnect-MgGraph
Disconnect-ExchangeOnline -Confirm:$false
```

---

## Conditional Access Policy

Create Conditional Access policy requiring MFA for administrators.

```powershell
<#
.SYNOPSIS
    Create Conditional Access Policy for MFA

.DESCRIPTION
    Creates a Conditional Access policy requiring MFA.
    Policy is created in report-only mode for safe testing.

.PARAMETER PolicyName
    Name for the policy

.PARAMETER IncludeAllUsers
    Apply to all users (default: false, admins only)
#>

#Requires -Modules Microsoft.Graph

param(
    [string]$PolicyName = "Require MFA for Administrators",
    [switch]$IncludeAllUsers,
    [switch]$Enforce
)

Connect-MgGraph -Scopes "Policy.ReadWrite.ConditionalAccess", "Directory.Read.All"

# Get admin role IDs
$adminRoles = @(
    "62e90394-69f5-4237-9190-012177145e10"  # Global Administrator
    "194ae4cb-b126-40b2-bd5b-6091b380977d"  # Security Administrator
    "f28a1f50-f6e7-4571-818b-6a12f2af6b6c"  # SharePoint Administrator
    "29232cdf-9323-42fd-ade2-1d097af3e4de"  # Exchange Administrator
    "fe930be7-5e62-47db-91af-98c3a49a38b1"  # User Administrator
)

# Build conditions
$conditions = @{
    Users = @{
        IncludeRoles = if ($IncludeAllUsers) { $null } else { $adminRoles }
        IncludeUsers = if ($IncludeAllUsers) { @("All") } else { $null }
        ExcludeUsers = @("GuestsOrExternalUsers")
    }
    Applications = @{
        IncludeApplications = @("All")
    }
    ClientAppTypes = @("browser", "mobileAppsAndDesktopClients")
}

# Remove null entries
if ($IncludeAllUsers) {
    $conditions.Users.Remove("IncludeRoles")
} else {
    $conditions.Users.Remove("IncludeUsers")
}

$grantControls = @{
    BuiltInControls = @("mfa")
    Operator = "OR"
}

$state = if ($Enforce) { "enabled" } else { "enabledForReportingButNotEnforced" }

$policyParams = @{
    DisplayName   = $PolicyName
    State         = $state
    Conditions    = $conditions
    GrantControls = $grantControls
}

try {
    $policy = New-MgIdentityConditionalAccessPolicy -BodyParameter $policyParams
    Write-Host "Policy created successfully" -ForegroundColor Green
    Write-Host "  Name: $($policy.DisplayName)"
    Write-Host "  ID: $($policy.Id)"
    Write-Host "  State: $state"

    if (-not $Enforce) {
        Write-Host "`nPolicy is in REPORT-ONLY mode." -ForegroundColor Yellow
        Write-Host "Monitor sign-in logs before enforcing."
        Write-Host "To enforce: Update policy state to 'enabled' in Azure AD portal"
    }
} catch {
    Write-Host "Error creating policy: $_" -ForegroundColor Red
}

Disconnect-MgGraph
```

---

## Bulk User Provisioning

Create users from CSV with license assignment.

```powershell
<#
.SYNOPSIS
    Bulk User Provisioning from CSV

.DESCRIPTION
    Creates users from CSV file with automatic license assignment.

.PARAMETER CsvPath
    Path to CSV file with columns: DisplayName, UserPrincipalName, Department, JobTitle

.PARAMETER LicenseSku
    License SKU to assign (e.g., ENTERPRISEPACK for E3)

.PARAMETER Password
    Initial password (auto-generated if not provided)
#>

#Requires -Modules Microsoft.Graph

param(
    [Parameter(Mandatory)]
    [string]$CsvPath,

    [string]$LicenseSku = "ENTERPRISEPACK",

    [string]$Password,

    [switch]$WhatIf
)

Connect-MgGraph -Scopes "User.ReadWrite.All", "Directory.ReadWrite.All"

# Validate CSV
if (-not (Test-Path $CsvPath)) {
    Write-Host "CSV file not found: $CsvPath" -ForegroundColor Red
    exit 1
}

$users = Import-Csv $CsvPath
Write-Host "Found $($users.Count) users in CSV" -ForegroundColor Cyan

# Get license SKU ID
$license = Get-MgSubscribedSku -All | Where-Object { $_.SkuPartNumber -eq $LicenseSku }
if (-not $license) {
    Write-Host "License SKU not found: $LicenseSku" -ForegroundColor Red
    Write-Host "Available SKUs:"
    Get-MgSubscribedSku -All | ForEach-Object { Write-Host "  $($_.SkuPartNumber)" }
    exit 1
}

$results = @()
$successCount = 0
$errorCount = 0

foreach ($user in $users) {
    $upn = $user.UserPrincipalName

    if ($WhatIf) {
        Write-Host "[WhatIf] Would create: $upn" -ForegroundColor Yellow
        continue
    }

    # Generate password if not provided
    $userPassword = if ($Password) { $Password } else {
        -join ((65..90) + (97..122) + (48..57) + (33,35,36,37) | Get-Random -Count 16 | ForEach-Object { [char]$_ })
    }

    $userParams = @{
        DisplayName       = $user.DisplayName
        UserPrincipalName = $upn
        MailNickname      = $upn.Split("@")[0]
        AccountEnabled    = $true
        Department        = $user.Department
        JobTitle          = $user.JobTitle
        UsageLocation     = "US"  # Required for license assignment
        PasswordProfile   = @{
            Password                             = $userPassword
            ForceChangePasswordNextSignIn        = $true
            ForceChangePasswordNextSignInWithMfa = $true
        }
    }

    try {
        # Create user
        $newUser = New-MgUser -BodyParameter $userParams
        Write-Host "Created: $upn" -ForegroundColor Green

        # Assign license
        $licenseParams = @{
            AddLicenses = @(@{ SkuId = $license.SkuId })
            RemoveLicenses = @()
        }
        Set-MgUserLicense -UserId $newUser.Id -BodyParameter $licenseParams
        Write-Host "  License assigned: $LicenseSku" -ForegroundColor Cyan

        $successCount++
        $results += [PSCustomObject]@{
            UserPrincipalName = $upn
            Status            = "Success"
            Password          = $userPassword
            Message           = "Created and licensed"
        }
    } catch {
        Write-Host "Error for $upn : $_" -ForegroundColor Red
        $errorCount++
        $results += [PSCustomObject]@{
            UserPrincipalName = $upn
            Status            = "Failed"
            Password          = ""
            Message           = $_.Exception.Message
        }
    }
}

# Export results
if (-not $WhatIf) {
    $resultsPath = "UserProvisioning_$(Get-Date -Format 'yyyyMMdd_HHmmss').csv"
    $results | Export-Csv -Path $resultsPath -NoTypeInformation
    Write-Host "`nResults saved to: $resultsPath" -ForegroundColor Green
    Write-Host "Success: $successCount | Errors: $errorCount"
}

Disconnect-MgGraph
```

**CSV Format:**

```csv
DisplayName,UserPrincipalName,Department,JobTitle
John Smith,john.smith@contoso.com,Engineering,Developer
Jane Doe,jane.doe@contoso.com,Marketing,Manager
```

---

## User Offboarding

Secure user offboarding with mailbox conversion and access removal.

```powershell
<#
.SYNOPSIS
    Secure User Offboarding

.DESCRIPTION
    Performs secure offboarding: disables account, revokes sessions,
    converts mailbox to shared, removes licenses, sets forwarding.

.PARAMETER UserPrincipalName
    UPN of user to offboard

.PARAMETER ForwardTo
    Email to forward messages to (optional)

.PARAMETER RetainMailbox
    Keep mailbox as shared (default: true)
#>

#Requires -Modules Microsoft.Graph, ExchangeOnlineManagement

param(
    [Parameter(Mandatory)]
    [string]$UserPrincipalName,

    [string]$ForwardTo,

    [switch]$RetainMailbox = $true,

    [switch]$WhatIf
)

Connect-MgGraph -Scopes "User.ReadWrite.All", "Directory.ReadWrite.All"
Connect-ExchangeOnline

Write-Host "Starting offboarding for: $UserPrincipalName" -ForegroundColor Cyan

$user = Get-MgUser -UserId $UserPrincipalName -ErrorAction SilentlyContinue
if (-not $user) {
    Write-Host "User not found: $UserPrincipalName" -ForegroundColor Red
    exit 1
}

$actions = @()

# 1. Disable account
if (-not $WhatIf) {
    Update-MgUser -UserId $user.Id -AccountEnabled:$false
}
$actions += "Disabled account"
Write-Host "[1/6] Account disabled" -ForegroundColor Green

# 2. Revoke all sessions
if (-not $WhatIf) {
    Revoke-MgUserSignInSession -UserId $user.Id
}
$actions += "Revoked all sessions"
Write-Host "[2/6] Sessions revoked" -ForegroundColor Green

# 3. Reset password
$newPassword = -join ((65..90) + (97..122) + (48..57) | Get-Random -Count 32 | ForEach-Object { [char]$_ })
if (-not $WhatIf) {
    $passwordProfile = @{
        Password                      = $newPassword
        ForceChangePasswordNextSignIn = $true
    }
    Update-MgUser -UserId $user.Id -PasswordProfile $passwordProfile
}
$actions += "Reset password"
Write-Host "[3/6] Password reset" -ForegroundColor Green

# 4. Remove from groups
$groups = Get-MgUserMemberOf -UserId $user.Id -All
$groupCount = 0
foreach ($group in $groups) {
    if ($group.AdditionalProperties.'@odata.type' -eq '#microsoft.graph.group') {
        if (-not $WhatIf) {
            Remove-MgGroupMemberByRef -GroupId $group.Id -DirectoryObjectId $user.Id -ErrorAction SilentlyContinue
        }
        $groupCount++
    }
}
$actions += "Removed from $groupCount groups"
Write-Host "[4/6] Removed from $groupCount groups" -ForegroundColor Green

# 5. Convert mailbox to shared (if retaining)
if ($RetainMailbox) {
    if (-not $WhatIf) {
        Set-Mailbox -Identity $UserPrincipalName -Type Shared
    }
    $actions += "Converted mailbox to shared"
    Write-Host "[5/6] Mailbox converted to shared" -ForegroundColor Green

    # Set forwarding if specified
    if ($ForwardTo) {
        if (-not $WhatIf) {
            Set-Mailbox -Identity $UserPrincipalName -ForwardingAddress $ForwardTo
        }
        $actions += "Mail forwarding set to $ForwardTo"
        Write-Host "  Forwarding to: $ForwardTo" -ForegroundColor Cyan
    }
} else {
    Write-Host "[5/6] Mailbox retention skipped" -ForegroundColor Yellow
}

# 6. Remove licenses
$licenses = Get-MgUserLicenseDetail -UserId $user.Id
if ($licenses -and -not $WhatIf) {
    $licenseParams = @{
        AddLicenses    = @()
        RemoveLicenses = $licenses.SkuId
    }
    Set-MgUserLicense -UserId $user.Id -BodyParameter $licenseParams
}
$actions += "Removed $($licenses.Count) licenses"
Write-Host "[6/6] Removed $($licenses.Count) licenses" -ForegroundColor Green

# Summary
Write-Host "`n=== Offboarding Complete ===" -ForegroundColor Green
Write-Host "User: $UserPrincipalName"
Write-Host "Actions taken:"
$actions | ForEach-Object { Write-Host "  - $_" }

if ($WhatIf) {
    Write-Host "`n[WhatIf] No changes were made" -ForegroundColor Yellow
}

Disconnect-MgGraph
Disconnect-ExchangeOnline -Confirm:$false
```

---

## License Management

Analyze license usage and optimize allocation.

```powershell
<#
.SYNOPSIS
    License Usage Analysis and Optimization

.DESCRIPTION
    Analyzes current license usage and identifies optimization opportunities.
#>

#Requires -Modules Microsoft.Graph

Connect-MgGraph -Scopes "Directory.Read.All", "User.Read.All"

Write-Host "Analyzing License Usage..." -ForegroundColor Cyan

$licenses = Get-MgSubscribedSku -All

$report = foreach ($lic in $licenses) {
    $available = $lic.PrepaidUnits.Enabled - $lic.ConsumedUnits
    $utilization = [math]::Round(($lic.ConsumedUnits / [math]::Max($lic.PrepaidUnits.Enabled, 1)) * 100, 1)

    [PSCustomObject]@{
        ProductName   = $lic.SkuPartNumber
        Total         = $lic.PrepaidUnits.Enabled
        Assigned      = $lic.ConsumedUnits
        Available     = $available
        Utilization   = "$utilization%"
        Status        = if ($utilization -gt 90) { "Critical" }
                       elseif ($utilization -gt 75) { "Warning" }
                       elseif ($utilization -lt 50) { "Underutilized" }
                       else { "Healthy" }
    }
}

$report | Format-Table -AutoSize

# Find users with unused licenses
Write-Host "`nChecking for inactive licensed users..." -ForegroundColor Yellow

$inactiveDate = (Get-Date).AddDays(-90)
$inactiveLicensed = Get-MgUser -All -Property Id,DisplayName,UserPrincipalName,SignInActivity,AssignedLicenses |
    Where-Object {
        $_.AssignedLicenses.Count -gt 0 -and
        $_.SignInActivity.LastSignInDateTime -and
        $_.SignInActivity.LastSignInDateTime -lt $inactiveDate
    } |
    Select-Object DisplayName, UserPrincipalName,
        @{N='LastSignIn';E={$_.SignInActivity.LastSignInDateTime}},
        @{N='LicenseCount';E={$_.AssignedLicenses.Count}}

if ($inactiveLicensed) {
    Write-Host "Found $($inactiveLicensed.Count) inactive users with licenses:" -ForegroundColor Yellow
    $inactiveLicensed | Format-Table -AutoSize
} else {
    Write-Host "No inactive licensed users found" -ForegroundColor Green
}

# Export
$report | Export-Csv -Path "LicenseAnalysis_$(Get-Date -Format 'yyyyMMdd').csv" -NoTypeInformation

Disconnect-MgGraph
```

---

## DNS Records Configuration

Generate DNS records for custom domain setup.

```powershell
<#
.SYNOPSIS
    Generate DNS Records for Microsoft 365

.DESCRIPTION
    Outputs required DNS records for custom domain verification and services.

.PARAMETER Domain
    Custom domain name
#>

param(
    [Parameter(Mandatory)]
    [string]$Domain
)

Write-Host "DNS Records for: $Domain" -ForegroundColor Cyan
Write-Host "=" * 60

Write-Host "`n### MX Record (Email)" -ForegroundColor Yellow
Write-Host "Type: MX"
Write-Host "Host: @"
Write-Host "Points to: $Domain.mail.protection.outlook.com"
Write-Host "Priority: 0"

Write-Host "`n### SPF Record (Email Authentication)" -ForegroundColor Yellow
Write-Host "Type: TXT"
Write-Host "Host: @"
Write-Host "Value: v=spf1 include:spf.protection.outlook.com -all"

Write-Host "`n### Autodiscover (Outlook Configuration)" -ForegroundColor Yellow
Write-Host "Type: CNAME"
Write-Host "Host: autodiscover"
Write-Host "Points to: autodiscover.outlook.com"

Write-Host "`n### DKIM Records (Email Signing)" -ForegroundColor Yellow
$domainKey = $Domain.Replace(".", "-")
Write-Host "Type: CNAME"
Write-Host "Host: selector1._domainkey"
Write-Host "Points to: selector1-$domainKey._domainkey.{tenant}.onmicrosoft.com"
Write-Host ""
Write-Host "Type: CNAME"
Write-Host "Host: selector2._domainkey"
Write-Host "Points to: selector2-$domainKey._domainkey.{tenant}.onmicrosoft.com"

Write-Host "`n### DMARC Record (Email Policy)" -ForegroundColor Yellow
Write-Host "Type: TXT"
Write-Host "Host: _dmarc"
Write-Host "Value: v=DMARC1; p=quarantine; rua=mailto:dmarc@$Domain"

Write-Host "`n### Teams/Skype Records" -ForegroundColor Yellow
Write-Host "Type: CNAME"
Write-Host "Host: sip"
Write-Host "Points to: sipdir.online.lync.com"
Write-Host ""
Write-Host "Type: CNAME"
Write-Host "Host: lyncdiscover"
Write-Host "Points to: webdir.online.lync.com"
Write-Host ""
Write-Host "Type: SRV"
Write-Host "Service: _sip._tls"
Write-Host "Port: 443"
Write-Host "Target: sipdir.online.lync.com"
Write-Host ""
Write-Host "Type: SRV"
Write-Host "Service: _sipfederationtls._tcp"
Write-Host "Port: 5061"
Write-Host "Target: sipfed.online.lync.com"

Write-Host "`n### MDM Enrollment (Intune)" -ForegroundColor Yellow
Write-Host "Type: CNAME"
Write-Host "Host: enterpriseregistration"
Write-Host "Points to: enterpriseregistration.windows.net"
Write-Host ""
Write-Host "Type: CNAME"
Write-Host "Host: enterpriseenrollment"
Write-Host "Points to: enterpriseenrollment.manage.microsoft.com"

Write-Host "`n" + "=" * 60 -ForegroundColor Cyan
Write-Host "Verify DNS propagation: nslookup -type=mx $Domain"
Write-Host "Note: DNS changes may take 24-48 hours to propagate"
```

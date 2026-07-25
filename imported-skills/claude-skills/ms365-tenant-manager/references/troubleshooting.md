# Troubleshooting Guide

Common issues and solutions for Microsoft 365 tenant administration.

---

## Table of Contents

- [Authentication Errors](#authentication-errors)
- [PowerShell Module Issues](#powershell-module-issues)
- [Permission Problems](#permission-problems)
- [License Assignment Failures](#license-assignment-failures)
- [DNS and Domain Issues](#dns-and-domain-issues)
- [Conditional Access Lockouts](#conditional-access-lockouts)
- [Mailbox Issues](#mailbox-issues)

---

## Authentication Errors

### "AADSTS50076: MFA Required"

**Cause:** User requires MFA but hasn't completed it.

**Solutions:**
1. Complete MFA registration at https://aka.ms/mfasetup
2. Use interactive authentication:
   ```powershell
   Connect-MgGraph -Scopes "User.Read.All" -UseDeviceAuthentication
   ```
3. Check Conditional Access policies excluding the user

### "AADSTS65001: User hasn't consented"

**Cause:** Application requires permissions user hasn't granted.

**Solutions:**
1. Grant admin consent in Azure AD portal
2. Use admin account for initial consent:
   ```powershell
   Connect-MgGraph -Scopes "User.ReadWrite.All" -ContextScope Process
   ```
3. Add application to enterprise applications with pre-consent

### "AADSTS700016: Application not found"

**Cause:** App registration missing or incorrect tenant.

**Solutions:**
1. Verify app ID in Azure AD > App registrations
2. Check multi-tenant setting if cross-tenant
3. Re-register application if needed

### "Access Denied" Despite Admin Role

**Causes:**
- PIM role not activated
- Role assignment pending
- Conditional Access blocking

**Solutions:**
1. Activate PIM role:
   - Go to Azure AD > Privileged Identity Management
   - Activate required role
2. Wait 5-10 minutes for role propagation
3. Check Conditional Access policies in report-only mode

---

## PowerShell Module Issues

### Module Not Found

**Error:** `The term 'Connect-MgGraph' is not recognized`

**Solutions:**
```powershell
# Install module
Install-Module Microsoft.Graph -Scope CurrentUser -Force

# If already installed, import explicitly
Import-Module Microsoft.Graph

# Check installation
Get-InstalledModule Microsoft.Graph
```

### Module Version Conflicts

**Error:** `Assembly with same name already loaded`

**Solutions:**
```powershell
# Remove all versions
Get-Module Microsoft.Graph* | Remove-Module -Force

# Clear cache
Remove-Item "$env:USERPROFILE\.local\share\powershell\*" -Recurse -Force

# Reinstall
Install-Module Microsoft.Graph -Force -AllowClobber
```

### Exchange Online Connection Failures

**Error:** `Connecting to remote server failed`

**Solutions:**
```powershell
# Use modern authentication
Connect-ExchangeOnline -UserPrincipalName admin@tenant.com

# If MFA issues, use device code
Connect-ExchangeOnline -Device

# Check WinRM service
Get-Service WinRM | Start-Service
```

### Graph API Throttling

**Error:** `429 Too Many Requests`

**Solutions:**
1. Implement retry logic:
   ```powershell
   $retryCount = 0
   $maxRetries = 3
   do {
       try {
           $result = Get-MgUser -All
           break
       } catch {
           if ($_.Exception.Response.StatusCode -eq 429) {
               $retryAfter = $_.Exception.Response.Headers['Retry-After']
               Start-Sleep -Seconds ([int]$retryAfter + 5)
               $retryCount++
           } else { throw }
       }
   } while ($retryCount -lt $maxRetries)
   ```
2. Reduce batch sizes
3. Use delta queries for incremental updates

---

## Permission Problems

### Insufficient Privileges for User Creation

**Error:** `Insufficient privileges to complete the operation`

**Required Permissions:**
- User Administrator role
- OR User.ReadWrite.All Graph permission

**Solutions:**
1. Verify role assignment:
   ```powershell
   Get-MgDirectoryRoleMember -DirectoryRoleId (Get-MgDirectoryRole -Filter "displayName eq 'User Administrator'").Id
   ```
2. Request role assignment or PIM activation
3. Use service principal with appropriate permissions

### Cannot Modify Another Admin

**Error:** `Cannot update privileged user`

**Cause:** Attempting to modify user with equal or higher privileges.

**Solutions:**
1. Use account with higher privilege level
2. Global Admin required to modify other Global Admins
3. Remove target's admin role first (if appropriate)

### Application Permission vs Delegated

**Issue:** Script works interactively but fails in automation

**Solution:** Use application permissions for automation:
```powershell
# Application authentication (daemon/service)
$clientId = "app-id"
$tenantId = "tenant-id"
$clientSecret = ConvertTo-SecureString "secret" -AsPlainText -Force
$credential = New-Object System.Management.Automation.PSCredential($clientId, $clientSecret)

Connect-MgGraph -ClientSecretCredential $credential -TenantId $tenantId
```

---

## License Assignment Failures

### "Usage location must be specified"

**Error:** `License assignment failed because UsageLocation is not set`

**Solution:**
```powershell
# Set usage location before license assignment
Update-MgUser -UserId user@tenant.com -UsageLocation "US"

# Then assign license
$license = @{
    AddLicenses = @(@{SkuId = "sku-id"})
    RemoveLicenses = @()
}
Set-MgUserLicense -UserId user@tenant.com -BodyParameter $license
```

### "No available licenses"

**Error:** `License quota exceeded`

**Solutions:**
1. Check available licenses:
   ```powershell
   Get-MgSubscribedSku | Select-Object SkuPartNumber,
       @{N='Available';E={$_.PrepaidUnits.Enabled - $_.ConsumedUnits}}
   ```
2. Remove licenses from inactive users
3. Purchase additional licenses

### Conflicting Service Plans

**Error:** `Conflicting service plans`

**Cause:** User has license with overlapping services.

**Solution:**
```powershell
# Check current licenses
Get-MgUserLicenseDetail -UserId user@tenant.com |
    Select-Object SkuPartNumber, @{N='Plans';E={$_.ServicePlans.ServicePlanName}}

# Remove conflicting license first
$remove = @{
    AddLicenses = @()
    RemoveLicenses = @("conflicting-sku-id")
}
Set-MgUserLicense -UserId user@tenant.com -BodyParameter $remove

# Then add new license
```

---

## DNS and Domain Issues

### Domain Verification Failing

**Error:** `Domain verification record not found`

**Solutions:**
1. Verify TXT record:
   ```bash
   nslookup -type=TXT domain.com
   ```
2. Check for typos in record value
3. Wait 24-48 hours for propagation
4. Try alternate verification (MX record)

### MX Record Not Resolving

**Error:** `Mail flow disrupted`

**Diagnostic:**
```bash
nslookup -type=MX domain.com
# Should return: domain.com.mail.protection.outlook.com
```

**Solutions:**
1. Verify MX record points to `domain.com.mail.protection.outlook.com`
2. Priority should be 0 or lowest number
3. Remove conflicting MX records

### SPF Record Issues

**Error:** `SPF validation failed`

**Correct SPF:**
```
v=spf1 include:spf.protection.outlook.com -all
```

**Common Mistakes:**
- Multiple SPF records (only one allowed)
- Missing `-all` or using `~all`
- Too many DNS lookups (max 10)

**Check:**
```bash
nslookup -type=TXT domain.com | findstr spf
```

---

## Conditional Access Lockouts

### Locked Out by MFA Policy

**Symptoms:** Cannot sign in, MFA loop

**Immediate Actions:**
1. Use emergency access account
2. Sign in from trusted location/device
3. Contact admin to temporarily exclude user

**Resolution:**
```powershell
# Add user to CA exclusion group
$group = Get-MgGroup -Filter "displayName eq 'CA-Excluded-Users'"
New-MgGroupMember -GroupId $group.Id -DirectoryObjectId (Get-MgUser -UserId user@tenant.com).Id
```

### Policy Conflicts

**Symptoms:** Unexpected blocks, inconsistent behavior

**Diagnostic:**
1. Check sign-in logs: Azure AD > Sign-in logs
2. Filter by user, check "Conditional Access" tab
3. Review which policies applied/failed

**Resolution:**
1. Review all policies in report-only mode
2. Check for conflicting conditions
3. Ensure proper policy ordering

### Break-Glass Procedure

**When to use:** Complete admin lockout

**Steps:**
1. Sign in with emergency access account
2. Go to Azure AD > Security > Conditional Access
3. Set all policies to "Report-only"
4. Diagnose and fix root cause
5. Re-enable policies gradually

---

## Mailbox Issues

### Mailbox Not Provisioning

**Error:** `Mailbox doesn't exist`

**Causes:**
- License not assigned
- License assignment pending
- User created without Exchange license

**Solutions:**
1. Verify license:
   ```powershell
   Get-MgUserLicenseDetail -UserId user@tenant.com
   ```
2. Wait 5-10 minutes after license assignment
3. Force mailbox provisioning:
   ```powershell
   # Reassign license
   Set-MgUserLicense -UserId user@tenant.com -BodyParameter @{
       RemoveLicenses = @("sku-id")
       AddLicenses = @()
   }
   Start-Sleep -Seconds 60
   Set-MgUserLicense -UserId user@tenant.com -BodyParameter @{
       AddLicenses = @(@{SkuId = "sku-id"})
       RemoveLicenses = @()
   }
   ```

### Mailbox Size Limit

**Error:** `Mailbox quota exceeded`

**Solutions:**
```powershell
# Check current quota
Get-Mailbox user@tenant.com | Select-Object ProhibitSendQuota, ProhibitSendReceiveQuota

# Increase quota (if license allows)
Set-Mailbox user@tenant.com -ProhibitSendQuota 99GB -ProhibitSendReceiveQuota 100GB

# Or enable archive
Enable-Mailbox user@tenant.com -Archive
```

### Mail Flow Issues

**Diagnostic:**
```powershell
# Test mail flow
Test-Mailflow -TargetEmailAddress external@gmail.com

# Check mail flow rules
Get-TransportRule | Where-Object {$_.State -eq 'Enabled'} | Select-Object Name, Priority, Conditions

# Check connectors
Get-InboundConnector
Get-OutboundConnector
```

**Common Fixes:**
1. Check transport rules for blocks
2. Verify connector configuration
3. Check ATP/spam policies
4. Review quarantine for false positives

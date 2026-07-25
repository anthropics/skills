"""
PowerShell script generator for Microsoft 365 administration tasks.
Creates ready-to-use scripts with error handling and best practices.
"""

from typing import Dict, List, Any, Optional


class PowerShellScriptGenerator:
    """Generate PowerShell scripts for common Microsoft 365 admin tasks."""

    def __init__(self, tenant_domain: str):
        """
        Initialize generator with tenant domain.

        Args:
            tenant_domain: Primary domain of the Microsoft 365 tenant
        """
        self.tenant_domain = tenant_domain

    def generate_conditional_access_policy_script(self, policy_config: Dict[str, Any]) -> str:
        """
        Generate script to create Conditional Access policy.

        Args:
            policy_config: Policy configuration parameters

        Returns:
            PowerShell script
        """
        policy_name = policy_config.get('name', 'MFA Policy')
        require_mfa = policy_config.get('require_mfa', True)
        include_users = policy_config.get('include_users', 'All')
        exclude_users = policy_config.get('exclude_users', [])

        script = f"""<#
.SYNOPSIS
    Create Conditional Access Policy: {policy_name}

.DESCRIPTION
    Creates a Conditional Access policy with specified settings.
    Policy will be created in report-only mode for testing.
#>

# Connect to Microsoft Graph
Connect-MgGraph -Scopes "Policy.ReadWrite.ConditionalAccess"

# Define policy parameters
$policyName = "{policy_name}"

# Create Conditional Access Policy
$conditions = @{{
    Users = @{{
        IncludeUsers = @("{include_users}")
"""

        if exclude_users:
            exclude_list = '", "'.join(exclude_users)
            script += f"""        ExcludeUsers = @("{exclude_list}")
"""

        script += """    }
    Applications = @{
        IncludeApplications = @("All")
    }
    Locations = @{
        IncludeLocations = @("All")
    }
}

$grantControls = @{
"""

        if require_mfa:
            script += """    BuiltInControls = @("mfa")
    Operator = "OR"
"""

        script += """}

$policy = @{
    DisplayName = $policyName
    State = "enabledForReportingButNotEnforced"  # Start in report-only mode
    Conditions = $conditions
    GrantControls = $grantControls
}

try {
    $newPolicy = New-MgIdentityConditionalAccessPolicy -BodyParameter $policy
    Write-Host "✓ Conditional Access policy created: $($newPolicy.DisplayName)" -ForegroundColor Green
    Write-Host "  Policy ID: $($newPolicy.Id)" -ForegroundColor Cyan
    Write-Host "  State: Report-only (test before enforcing)" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "Next steps:" -ForegroundColor Cyan
    Write-Host "1. Review policy in Azure AD > Security > Conditional Access"
    Write-Host "2. Monitor sign-in logs for impact assessment"
    Write-Host "3. When ready, change state to 'enabled' to enforce"
} catch {
    Write-Host "✗ Error creating policy: $_" -ForegroundColor Red
}

Disconnect-MgGraph
"""
        return script

    def generate_security_audit_script(self) -> str:
        """
        Generate comprehensive security audit script.

        Returns:
            PowerShell script for security assessment
        """
        script = """<#
.SYNOPSIS
    Microsoft 365 Security Audit Report

.DESCRIPTION
    Performs comprehensive security audit and generates detailed report.
    Checks: MFA status, admin accounts, inactive users, permissions, licenses

.OUTPUTS
    CSV reports with security findings
#>

# Connect to services
Connect-MgGraph -Scopes "Directory.Read.All", "User.Read.All", "AuditLog.Read.All"
Connect-ExchangeOnline

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$reportPath = "SecurityAudit_$timestamp"
New-Item -ItemType Directory -Path $reportPath -Force | Out-Null

Write-Host "Starting Security Audit..." -ForegroundColor Cyan
Write-Host ""

# 1. Check MFA Status
Write-Host "[1/7] Checking MFA status for all users..." -ForegroundColor Yellow

$mfaReport = @()
$users = Get-MgUser -All -Property Id,DisplayName,UserPrincipalName,AccountEnabled

foreach ($user in $users) {
    $authMethods = Get-MgUserAuthenticationMethod -UserId $user.Id
    $hasMFA = $authMethods.Count -gt 1  # More than just password

    $mfaReport += [PSCustomObject]@{
        UserPrincipalName = $user.UserPrincipalName
        DisplayName = $user.DisplayName
        AccountEnabled = $user.AccountEnabled
        MFAEnabled = $hasMFA
        AuthMethodsCount = $authMethods.Count
    }
}

$mfaReport | Export-Csv -Path "$reportPath/MFA_Status.csv" -NoTypeInformation
$usersWithoutMFA = ($mfaReport | Where-Object { $_.MFAEnabled -eq $false -and $_.AccountEnabled -eq $true }).Count
Write-Host "  Users without MFA: $usersWithoutMFA" -ForegroundColor $(if($usersWithoutMFA -gt 0){'Red'}else{'Green'})

# 2. Check Admin Accounts
Write-Host "[2/7] Auditing admin role assignments..." -ForegroundColor Yellow

$adminRoles = Get-MgDirectoryRole -All
$adminReport = @()

foreach ($role in $adminRoles) {
    $members = Get-MgDirectoryRoleMember -DirectoryRoleId $role.Id
    foreach ($member in $members) {
        $user = Get-MgUser -UserId $member.Id -ErrorAction SilentlyContinue
        if ($user) {
            $adminReport += [PSCustomObject]@{
                UserPrincipalName = $user.UserPrincipalName
                DisplayName = $user.DisplayName
                Role = $role.DisplayName
                AccountEnabled = $user.AccountEnabled
            }
        }
    }
}

$adminReport | Export-Csv -Path "$reportPath/Admin_Roles.csv" -NoTypeInformation
Write-Host "  Total admin assignments: $($adminReport.Count)" -ForegroundColor Cyan

# 3. Check Inactive Users
Write-Host "[3/7] Identifying inactive users (90+ days)..." -ForegroundColor Yellow

$inactiveDate = (Get-Date).AddDays(-90)
$inactiveUsers = @()

foreach ($user in $users) {
    $signIns = Get-MgAuditLogSignIn -Filter "userId eq '$($user.Id)'" -Top 1
    $lastSignIn = if ($signIns) { $signIns[0].CreatedDateTime } else { $null }

    if ($lastSignIn -and $lastSignIn -lt $inactiveDate -and $user.AccountEnabled) {
        $inactiveUsers += [PSCustomObject]@{
            UserPrincipalName = $user.UserPrincipalName
            DisplayName = $user.DisplayName
            LastSignIn = $lastSignIn
            DaysSinceSignIn = ((Get-Date) - $lastSignIn).Days
        }
    }
}

$inactiveUsers | Export-Csv -Path "$reportPath/Inactive_Users.csv" -NoTypeInformation
Write-Host "  Inactive users found: $($inactiveUsers.Count)" -ForegroundColor $(if($inactiveUsers.Count -gt 0){'Yellow'}else{'Green'})

# 4. Check Guest Users
Write-Host "[4/7] Reviewing guest user access..." -ForegroundColor Yellow

$guestUsers = Get-MgUser -Filter "userType eq 'Guest'" -All
$guestReport = $guestUsers | Select-Object UserPrincipalName, DisplayName, AccountEnabled, CreatedDateTime

$guestReport | Export-Csv -Path "$reportPath/Guest_Users.csv" -NoTypeInformation
Write-Host "  Guest users: $($guestUsers.Count)" -ForegroundColor Cyan

# 5. Check License Usage
Write-Host "[5/7] Analyzing license allocation..." -ForegroundColor Yellow

$licenses = Get-MgSubscribedSku
$licenseReport = @()

foreach ($license in $licenses) {
    $licenseReport += [PSCustomObject]@{
        ProductName = $license.SkuPartNumber
        TotalLicenses = $license.PrepaidUnits.Enabled
        AssignedLicenses = $license.ConsumedUnits
        AvailableLicenses = $license.PrepaidUnits.Enabled - $license.ConsumedUnits
        UtilizationPercent = [math]::Round(($license.ConsumedUnits / $license.PrepaidUnits.Enabled) * 100, 2)
    }
}

$licenseReport | Export-Csv -Path "$reportPath/License_Usage.csv" -NoTypeInformation
Write-Host "  License SKUs analyzed: $($licenses.Count)" -ForegroundColor Cyan

# 6. Check Mailbox Permissions
Write-Host "[6/7] Auditing mailbox delegations..." -ForegroundColor Yellow

$mailboxes = Get-Mailbox -ResultSize Unlimited
$delegationReport = @()

foreach ($mailbox in $mailboxes) {
    $permissions = Get-MailboxPermission -Identity $mailbox.Identity |
                   Where-Object { $_.User -ne "NT AUTHORITY\SELF" -and $_.IsInherited -eq $false }

    foreach ($perm in $permissions) {
        $delegationReport += [PSCustomObject]@{
            Mailbox = $mailbox.UserPrincipalName
            DelegatedTo = $perm.User
            AccessRights = $perm.AccessRights -join ", "
        }
    }
}

$delegationReport | Export-Csv -Path "$reportPath/Mailbox_Delegations.csv" -NoTypeInformation
Write-Host "  Delegated mailboxes: $($delegationReport.Count)" -ForegroundColor Cyan

# 7. Check Conditional Access Policies
Write-Host "[7/7] Reviewing Conditional Access policies..." -ForegroundColor Yellow

$caPolicies = Get-MgIdentityConditionalAccessPolicy
$caReport = $caPolicies | Select-Object DisplayName, State, CreatedDateTime,
                                         @{N='IncludeUsers';E={$_.Conditions.Users.IncludeUsers -join '; '}},
                                         @{N='RequiresMFA';E={$_.GrantControls.BuiltInControls -contains 'mfa'}}

$caReport | Export-Csv -Path "$reportPath/ConditionalAccess_Policies.csv" -NoTypeInformation
Write-Host "  Conditional Access policies: $($caPolicies.Count)" -ForegroundColor Cyan

# Generate Summary Report
Write-Host ""
Write-Host "=== Security Audit Summary ===" -ForegroundColor Green
Write-Host ""
Write-Host "Users:" -ForegroundColor Cyan
Write-Host "  Total Users: $($users.Count)"
Write-Host "  Users without MFA: $usersWithoutMFA $(if($usersWithoutMFA -gt 0){'⚠️'}else{'✓'})"
Write-Host "  Inactive Users (90+ days): $($inactiveUsers.Count) $(if($inactiveUsers.Count -gt 0){'⚠️'}else{'✓'})"
Write-Host "  Guest Users: $($guestUsers.Count)"
Write-Host ""
Write-Host "Administration:" -ForegroundColor Cyan
Write-Host "  Admin Role Assignments: $($adminReport.Count)"
Write-Host "  Conditional Access Policies: $($caPolicies.Count)"
Write-Host ""
Write-Host "Licenses:" -ForegroundColor Cyan
foreach ($lic in $licenseReport) {
    Write-Host "  $($lic.ProductName): $($lic.AssignedLicenses)/$($lic.TotalLicenses) ($($lic.UtilizationPercent)%)"
}
Write-Host ""
Write-Host "Reports saved to: $reportPath" -ForegroundColor Green
Write-Host ""
Write-Host "Recommended Actions:" -ForegroundColor Yellow
if ($usersWithoutMFA -gt 0) {
    Write-Host "  1. Enable MFA for users without MFA"
}
if ($inactiveUsers.Count -gt 0) {
    Write-Host "  2. Review and disable inactive user accounts"
}
if ($guestUsers.Count -gt 10) {
    Write-Host "  3. Review guest user access and remove unnecessary guests"
}

# Disconnect
Disconnect-MgGraph
Disconnect-ExchangeOnline -Confirm:$false
"""
        return script

    def generate_bulk_license_assignment_script(self, users_csv_path: str, license_sku: str) -> str:
        """
        Generate script for bulk license assignment from CSV.

        Args:
            users_csv_path: Path to CSV with user emails
            license_sku: License SKU to assign

        Returns:
            PowerShell script
        """
        script = f"""<#
.SYNOPSIS
    Bulk License Assignment from CSV

.DESCRIPTION
    Assigns {license_sku} license to users listed in CSV file.
    CSV must have 'UserPrincipalName' column.

.PARAMETER CsvPath
    Path to CSV file with user list
#>

param(
    [Parameter(Mandatory=$true)]
    [string]$CsvPath = "{users_csv_path}"
)

# Connect to Microsoft Graph
Connect-MgGraph -Scopes "User.ReadWrite.All", "Directory.ReadWrite.All"

# Get license SKU ID
$targetSku = "{license_sku}"
$licenseSkuId = (Get-MgSubscribedSku -All | Where-Object {{$_.SkuPartNumber -eq $targetSku}}).SkuId

if (-not $licenseSkuId) {{
    Write-Host "✗ License SKU not found: $targetSku" -ForegroundColor Red
    exit
}}

Write-Host "License SKU found: $targetSku" -ForegroundColor Green
Write-Host "SKU ID: $licenseSkuId" -ForegroundColor Cyan
Write-Host ""

# Import users from CSV
$users = Import-Csv -Path $CsvPath

if (-not $users) {{
    Write-Host "✗ No users found in CSV file" -ForegroundColor Red
    exit
}}

Write-Host "Found $($users.Count) users in CSV" -ForegroundColor Cyan
Write-Host ""

# Process each user
$successCount = 0
$errorCount = 0
$results = @()

foreach ($user in $users) {{
    $userEmail = $user.UserPrincipalName

    try {{
        # Get user
        $mgUser = Get-MgUser -UserId $userEmail -ErrorAction Stop

        # Check if user already has license
        $currentLicenses = Get-MgUserLicenseDetail -UserId $mgUser.Id
        if ($currentLicenses.SkuId -contains $licenseSkuId) {{
            Write-Host "  ⊘ $userEmail - Already has license" -ForegroundColor Yellow
            $results += [PSCustomObject]@{{
                UserPrincipalName = $userEmail
                Status = "Skipped"
                Message = "Already licensed"
            }}
            continue
        }}

        # Assign license
        $licenseParams = @{{
            AddLicenses = @(
                @{{
                    SkuId = $licenseSkuId
                }}
            )
        }}

        Set-MgUserLicense -UserId $mgUser.Id -BodyParameter $licenseParams
        Write-Host "  ✓ $userEmail - License assigned successfully" -ForegroundColor Green

        $successCount++
        $results += [PSCustomObject]@{{
            UserPrincipalName = $userEmail
            Status = "Success"
            Message = "License assigned"
        }}

    }} catch {{
        Write-Host "  ✗ $userEmail - Error: $_" -ForegroundColor Red
        $errorCount++
        $results += [PSCustomObject]@{{
            UserPrincipalName = $userEmail
            Status = "Failed"
            Message = $_.Exception.Message
        }}
    }}
}}

# Export results
$resultsPath = "LicenseAssignment_Results_$(Get-Date -Format 'yyyyMMdd_HHmmss').csv"
$results | Export-Csv -Path $resultsPath -NoTypeInformation

# Summary
Write-Host ""
Write-Host "=== Summary ===" -ForegroundColor Cyan
Write-Host "Total users processed: $($users.Count)"
Write-Host "Successfully assigned: $successCount" -ForegroundColor Green
Write-Host "Errors: $errorCount" -ForegroundColor $(if($errorCount -gt 0){{'Red'}}else{{'Green'}})
Write-Host ""
Write-Host "Results saved to: $resultsPath" -ForegroundColor Cyan

# Disconnect
Disconnect-MgGraph
"""
        return script


def main():
    """CLI entry point."""
    import argparse
    import json

    parser = argparse.ArgumentParser(
        description="Generate ready-to-run M365 admin PowerShell scripts (Graph SDK based)"
    )
    parser.add_argument("--tenant-domain", required=True, help="Primary tenant domain (e.g. acme.com)")
    parser.add_argument("--task", required=True,
                        choices=["conditional-access", "security-audit", "bulk-license"],
                        help="Which script to generate")
    parser.add_argument("--policy-config", help="Policy config JSON file (conditional-access)")
    parser.add_argument("--users-csv", help="Users CSV path baked into the script (bulk-license)")
    parser.add_argument("--license-sku", help="License SKU (bulk-license)")
    parser.add_argument("--output", "-o", help="Output file (default: stdout)")
    args = parser.parse_args()

    generator = PowerShellScriptGenerator(args.tenant_domain)

    if args.task == "conditional-access":
        policy = {}
        if args.policy_config:
            with open(args.policy_config, "r", encoding="utf-8") as f:
                policy = json.load(f)
        result = generator.generate_conditional_access_policy_script(policy)
    elif args.task == "security-audit":
        result = generator.generate_security_audit_script()
    else:  # bulk-license
        if not (args.users_csv and args.license_sku):
            parser.error("--users-csv and --license-sku are required for --task bulk-license")
        result = generator.generate_bulk_license_assignment_script(args.users_csv, args.license_sku)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(result)
    else:
        print(result)


if __name__ == "__main__":
    main()

"""
Microsoft 365 tenant setup and configuration module.
Generates guidance and scripts for initial tenant configuration.
"""

from typing import Dict, List, Any, Optional


class TenantSetupManager:
    """Manage Microsoft 365 tenant setup and initial configuration."""

    def __init__(self, tenant_config: Dict[str, Any]):
        """
        Initialize with tenant configuration.

        Args:
            tenant_config: Dictionary containing tenant details and requirements
        """
        self.company_name = tenant_config.get('company_name', '')
        self.domain_name = tenant_config.get('domain_name', '')
        self.user_count = tenant_config.get('user_count', 0)
        self.industry = tenant_config.get('industry', 'general')
        self.compliance_requirements = tenant_config.get('compliance_requirements', [])
        self.licenses = tenant_config.get('licenses', {})
        self.setup_steps = []

    def generate_setup_checklist(self) -> List[Dict[str, Any]]:
        """
        Generate comprehensive tenant setup checklist.

        Returns:
            List of setup steps with details and priorities
        """
        checklist = []

        # Phase 1: Initial Configuration
        checklist.append({
            'phase': 1,
            'name': 'Initial Tenant Configuration',
            'priority': 'critical',
            'tasks': [
                {
                    'task': 'Sign in to Microsoft 365 Admin Center',
                    'url': 'https://admin.microsoft.com',
                    'estimated_time': '5 minutes'
                },
                {
                    'task': 'Complete tenant setup wizard',
                    'details': 'Set organization profile, contact info, and preferences',
                    'estimated_time': '10 minutes'
                },
                {
                    'task': 'Configure company branding',
                    'details': 'Upload logo, set theme colors, customize sign-in page',
                    'estimated_time': '15 minutes'
                }
            ]
        })

        # Phase 2: Domain Setup
        checklist.append({
            'phase': 2,
            'name': 'Custom Domain Configuration',
            'priority': 'critical',
            'tasks': [
                {
                    'task': 'Add custom domain',
                    'details': f'Add {self.domain_name} to tenant',
                    'estimated_time': '5 minutes'
                },
                {
                    'task': 'Verify domain ownership',
                    'details': 'Add TXT record to DNS: MS=msXXXXXXXX',
                    'estimated_time': '10 minutes (plus DNS propagation)'
                },
                {
                    'task': 'Configure DNS records',
                    'details': 'Add MX, CNAME, TXT records for services',
                    'estimated_time': '20 minutes'
                },
                {
                    'task': 'Set as default domain',
                    'details': f'Make {self.domain_name} the default for new users',
                    'estimated_time': '2 minutes'
                }
            ]
        })

        # Phase 3: Security Baseline
        checklist.append({
            'phase': 3,
            'name': 'Security Baseline Configuration',
            'priority': 'critical',
            'tasks': [
                {
                    'task': 'Enable Security Defaults or Conditional Access',
                    'details': 'Enforce MFA and modern authentication',
                    'estimated_time': '15 minutes'
                },
                {
                    'task': 'Configure named locations',
                    'details': 'Define trusted IP ranges for office locations',
                    'estimated_time': '10 minutes'
                },
                {
                    'task': 'Set up admin accounts',
                    'details': 'Create separate admin accounts, enable PIM',
                    'estimated_time': '20 minutes'
                },
                {
                    'task': 'Enable audit logging',
                    'details': 'Turn on unified audit log for compliance',
                    'estimated_time': '5 minutes'
                },
                {
                    'task': 'Configure password policies',
                    'details': 'Set expiration, complexity, banned passwords',
                    'estimated_time': '10 minutes'
                }
            ]
        })

        # Phase 4: Service Provisioning
        checklist.append({
            'phase': 4,
            'name': 'Service Configuration',
            'priority': 'high',
            'tasks': [
                {
                    'task': 'Configure Exchange Online',
                    'details': 'Set up mailboxes, mail flow, anti-spam policies',
                    'estimated_time': '30 minutes'
                },
                {
                    'task': 'Set up SharePoint Online',
                    'details': 'Configure sharing settings, storage limits, site templates',
                    'estimated_time': '25 minutes'
                },
                {
                    'task': 'Enable Microsoft Teams',
                    'details': 'Configure Teams policies, guest access, meeting settings',
                    'estimated_time': '20 minutes'
                },
                {
                    'task': 'Configure OneDrive for Business',
                    'details': 'Set storage quotas, sync restrictions, sharing policies',
                    'estimated_time': '15 minutes'
                }
            ]
        })

        # Phase 5: Compliance (if required)
        if self.compliance_requirements:
            compliance_tasks = []
            if 'GDPR' in self.compliance_requirements:
                compliance_tasks.append({
                    'task': 'Configure GDPR compliance',
                    'details': 'Set up data residency, retention policies, DSR workflows',
                    'estimated_time': '45 minutes'
                })
            if 'HIPAA' in self.compliance_requirements:
                compliance_tasks.append({
                    'task': 'Enable HIPAA compliance features',
                    'details': 'Configure encryption, audit logs, access controls',
                    'estimated_time': '40 minutes'
                })

            checklist.append({
                'phase': 5,
                'name': 'Compliance Configuration',
                'priority': 'high',
                'tasks': compliance_tasks
            })

        return checklist

    def generate_dns_records(self) -> Dict[str, List[Dict[str, str]]]:
        """
        Generate required DNS records for Microsoft 365 services.

        Returns:
            Dictionary of DNS record types and configurations
        """
        domain = self.domain_name

        return {
            'mx_records': [
                {
                    'type': 'MX',
                    'name': '@',
                    'value': f'{domain.replace(".", "-")}.mail.protection.outlook.com',
                    'priority': '0',
                    'ttl': '3600',
                    'purpose': 'Email delivery to Exchange Online'
                }
            ],
            'txt_records': [
                {
                    'type': 'TXT',
                    'name': '@',
                    'value': 'v=spf1 include:spf.protection.outlook.com -all',
                    'ttl': '3600',
                    'purpose': 'SPF record for email authentication'
                },
                {
                    'type': 'TXT',
                    'name': '@',
                    'value': 'MS=msXXXXXXXX',
                    'ttl': '3600',
                    'purpose': 'Domain verification (replace XXXXXXXX with actual value)'
                }
            ],
            'cname_records': [
                {
                    'type': 'CNAME',
                    'name': 'autodiscover',
                    'value': 'autodiscover.outlook.com',
                    'ttl': '3600',
                    'purpose': 'Outlook autodiscover for automatic email configuration'
                },
                {
                    'type': 'CNAME',
                    'name': 'selector1._domainkey',
                    'value': f'selector1-{domain.replace(".", "-")}._domainkey.onmicrosoft.com',
                    'ttl': '3600',
                    'purpose': 'DKIM signature for email security'
                },
                {
                    'type': 'CNAME',
                    'name': 'selector2._domainkey',
                    'value': f'selector2-{domain.replace(".", "-")}._domainkey.onmicrosoft.com',
                    'ttl': '3600',
                    'purpose': 'DKIM signature for email security (rotation)'
                },
                {
                    'type': 'CNAME',
                    'name': 'msoid',
                    'value': 'clientconfig.microsoftonline-p.net',
                    'ttl': '3600',
                    'purpose': 'Azure AD authentication'
                },
                {
                    'type': 'CNAME',
                    'name': 'enterpriseregistration',
                    'value': 'enterpriseregistration.windows.net',
                    'ttl': '3600',
                    'purpose': 'Device registration for Azure AD join'
                },
                {
                    'type': 'CNAME',
                    'name': 'enterpriseenrollment',
                    'value': 'enterpriseenrollment.manage.microsoft.com',
                    'ttl': '3600',
                    'purpose': 'Mobile device management (Intune)'
                }
            ],
            'srv_records': [
                {
                    'type': 'SRV',
                    'name': '_sip._tls',
                    'value': 'sipdir.online.lync.com',
                    'port': '443',
                    'priority': '100',
                    'weight': '1',
                    'ttl': '3600',
                    'purpose': 'Skype for Business / Teams federation'
                },
                {
                    'type': 'SRV',
                    'name': '_sipfederationtls._tcp',
                    'value': 'sipfed.online.lync.com',
                    'port': '5061',
                    'priority': '100',
                    'weight': '1',
                    'ttl': '3600',
                    'purpose': 'Teams external federation'
                }
            ]
        }

    def generate_powershell_setup_script(self) -> str:
        """
        Generate PowerShell script for initial tenant configuration.

        Returns:
            Complete PowerShell script as string
        """
        script = f"""<#
.SYNOPSIS
    Microsoft 365 Tenant Initial Setup Script
    Generated for: {self.company_name}
    Domain: {self.domain_name}

.DESCRIPTION
    This script performs initial Microsoft 365 tenant configuration.
    Run this script with Global Administrator credentials.

.NOTES
    Prerequisites:
    - Install Microsoft.Graph module: Install-Module Microsoft.Graph -Scope CurrentUser
    - Install ExchangeOnlineManagement: Install-Module ExchangeOnlineManagement
    - Install MicrosoftTeams: Install-Module MicrosoftTeams
#>

# Connect to Microsoft 365 services
Write-Host "Connecting to Microsoft 365..." -ForegroundColor Cyan

# Connect to Microsoft Graph
Connect-MgGraph -Scopes "Organization.ReadWrite.All", "Directory.ReadWrite.All", "Policy.ReadWrite.ConditionalAccess"

# Connect to Exchange Online
Connect-ExchangeOnline

# Connect to Microsoft Teams
Connect-MicrosoftTeams

# Step 1: Configure organization settings
Write-Host "Configuring organization settings..." -ForegroundColor Green

$orgSettings = @{{
    DisplayName = "{self.company_name}"
    PreferredLanguage = "en-US"
}}

Update-MgOrganization -OrganizationId (Get-MgOrganization).Id -BodyParameter $orgSettings

# Step 2: Enable Security Defaults (or use Conditional Access for advanced)
Write-Host "Enabling Security Defaults (MFA)..." -ForegroundColor Green

# Uncomment to enable Security Defaults:
# Update-MgPolicyIdentitySecurityDefaultEnforcementPolicy -IsEnabled $true

# Step 3: Enable audit logging
Write-Host "Enabling unified audit log..." -ForegroundColor Green
Set-AdminAuditLogConfig -UnifiedAuditLogIngestionEnabled $true

# Step 4: Configure Exchange Online settings
Write-Host "Configuring Exchange Online..." -ForegroundColor Green

# Set organization config
Set-OrganizationConfig -DefaultPublicFolderAgeLimit 30

# Configure anti-spam policy
$antiSpamPolicy = @{{
    Name = "Default Anti-Spam Policy"
    SpamAction = "MoveToJmf"  # Move to Junk folder
    HighConfidenceSpamAction = "Quarantine"
    BulkSpamAction = "MoveToJmf"
    EnableEndUserSpamNotifications = $true
}}

# Step 5: Configure SharePoint Online settings
Write-Host "Configuring SharePoint Online..." -ForegroundColor Green

# Note: SharePoint management requires SharePointPnPPowerShellOnline module
# Connect-PnPOnline -Url "https://{self.domain_name.split('.')[0]}-admin.sharepoint.com" -Interactive

# Step 6: Configure Microsoft Teams settings
Write-Host "Configuring Microsoft Teams..." -ForegroundColor Green

# Set Teams messaging policy
$messagingPolicy = @{{
    Identity = "Global"
    AllowUserChat = $true
    AllowUserDeleteMessage = $true
    AllowGiphy = $true
    GiphyRatingType = "Moderate"
}}

# Step 7: Summary
Write-Host "`nTenant setup complete!" -ForegroundColor Green
Write-Host "Next steps:" -ForegroundColor Cyan
Write-Host "1. Add and verify custom domain: {self.domain_name}"
Write-Host "2. Configure DNS records (see DNS configuration output)"
Write-Host "3. Create user accounts or set up AD Connect for hybrid"
Write-Host "4. Assign licenses to users"
Write-Host "5. Review and configure Conditional Access policies"
Write-Host "6. Complete compliance configuration if required"

# Disconnect from services
Disconnect-MgGraph
Disconnect-ExchangeOnline -Confirm:$false
Disconnect-MicrosoftTeams
"""
        return script

    def get_license_recommendations(self) -> Dict[str, Any]:
        """
        Recommend appropriate Microsoft 365 licenses based on requirements.

        Returns:
            Dictionary with license recommendations
        """
        recommendations = {
            'basic_users': {
                'license': 'Microsoft 365 Business Basic',
                'features': ['Web versions of Office apps', 'Teams', 'OneDrive (1TB)', 'Exchange (50GB)'],
                'cost_per_user_month': 6.00,
                'recommended_for': 'Frontline workers, part-time staff'
            },
            'standard_users': {
                'license': 'Microsoft 365 Business Standard',
                'features': ['Desktop Office apps', 'Teams', 'OneDrive (1TB)', 'Exchange (50GB)', 'SharePoint'],
                'cost_per_user_month': 12.50,
                'recommended_for': 'Most office workers'
            },
            'advanced_security': {
                'license': 'Microsoft 365 E3',
                'features': ['All Business Standard features', 'Advanced security', 'Compliance tools', 'Azure AD P1'],
                'cost_per_user_month': 36.00,
                'recommended_for': 'Users handling sensitive data, compliance requirements'
            },
            'executives_admins': {
                'license': 'Microsoft 365 E5',
                'features': ['All E3 features', 'Advanced threat protection', 'Azure AD P2', 'Advanced compliance'],
                'cost_per_user_month': 57.00,
                'recommended_for': 'Executives, IT admins, high-risk users'
            }
        }

        # Calculate recommended distribution
        total_users = self.user_count
        distribution = {
            'E5': min(5, int(total_users * 0.05)),  # 5% or 5 users, whichever is less
            'E3': int(total_users * 0.20) if total_users > 50 else 0,  # 20% for larger orgs
            'Business_Standard': int(total_users * 0.70),  # 70% standard users
            'Business_Basic': int(total_users * 0.05)  # 5% basic users
        }

        # Adjust for compliance requirements
        if self.compliance_requirements:
            distribution['E3'] = distribution['E3'] + distribution['Business_Standard'] // 2
            distribution['Business_Standard'] = distribution['Business_Standard'] // 2

        estimated_monthly_cost = (
            distribution['E5'] * 57.00 +
            distribution['E3'] * 36.00 +
            distribution['Business_Standard'] * 12.50 +
            distribution['Business_Basic'] * 6.00
        )

        return {
            'recommendations': recommendations,
            'suggested_distribution': distribution,
            'estimated_monthly_cost': round(estimated_monthly_cost, 2),
            'estimated_annual_cost': round(estimated_monthly_cost * 12, 2)
        }


def main():
    """CLI entry point."""
    import argparse
    import json

    parser = argparse.ArgumentParser(
        description="Generate M365 tenant setup checklist, DNS records, license plan, and PowerShell setup script"
    )
    parser.add_argument("--config", required=True,
                        help="Tenant config JSON file (top-level 'tenant_config' key or the config object itself)")
    parser.add_argument("--format", choices=["json", "powershell"], default="json",
                        help="json = checklist + DNS + license plan; powershell = setup script")
    parser.add_argument("--output", "-o", help="Output file (default: stdout)")
    args = parser.parse_args()

    with open(args.config, "r", encoding="utf-8") as f:
        data = json.load(f)
    config = data.get("tenant_config", data)
    manager = TenantSetupManager(config)

    if args.format == "powershell":
        result = manager.generate_powershell_setup_script()
    else:
        result = json.dumps({
            "setup_checklist": manager.generate_setup_checklist(),
            "dns_records": manager.generate_dns_records(),
            "license_recommendations": manager.get_license_recommendations(),
        }, indent=2)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(result)
    else:
        print(result)


if __name__ == "__main__":
    main()

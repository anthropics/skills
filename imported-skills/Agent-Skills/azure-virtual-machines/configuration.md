# Azure Virtual Machines — Configuration

> This is a reference file for the main [SKILL.md](SKILL.md). This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

### Configuration
| Topic | URL |
|-------|-----|
| Configure attribute-based VM selection in Compute Fleet | https://learn.microsoft.com/en-us/azure/azure-compute-fleet/attribute-based-vm-selection |
| Modify capacity and VM sizes in Azure Compute Fleet | https://learn.microsoft.com/en-us/azure/azure-compute-fleet/modify-fleet |
| Configure Spot VM behavior in Azure Compute Fleet | https://learn.microsoft.com/en-us/azure/azure-compute-fleet/spot-vm-configuration |
| Inspect and manage Azure Linux AKS host packages | https://learn.microsoft.com/en-us/azure/azure-linux/aks-packages |
| Configure networking on Azure Linux with systemd-networkd | https://learn.microsoft.com/en-us/azure/azure-linux/configure-networking |
| Enable debuginfo repositories on Azure Linux | https://learn.microsoft.com/en-us/azure/azure-linux/install-debug-symbol-packages |
| Inspect and configure Azure Linux kernel parameters | https://learn.microsoft.com/en-us/azure/azure-linux/kernel-management |
| View logs and monitor system health on Azure Linux | https://learn.microsoft.com/en-us/azure/azure-linux/logging-monitoring |
| Discover and use Azure Linux package repositories | https://learn.microsoft.com/en-us/azure/azure-linux/package-repositories |
| Configure and deploy AKS pod sandboxing on Azure Linux | https://learn.microsoft.com/en-us/azure/azure-linux/pod-sandboxing-aks |
| Manage storage and filesystems on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/azure-linux/storage-file-system-management |
| Configure telemetry and monitoring for Azure Linux AKS clusters | https://learn.microsoft.com/en-us/azure/azure-linux/tutorial-monitor-azure-linux-aks |
| Enable automatic extension upgrades for Azure VMs and scale sets | https://learn.microsoft.com/en-us/azure/virtual-machines/automatic-extension-upgrade |
| Configure automatic guest patching for Azure VMs and scale sets | https://learn.microsoft.com/en-us/azure/virtual-machines/automatic-vm-guest-patching |
| Use Azure VM watch to collect in-VM health signals | https://learn.microsoft.com/en-us/azure/virtual-machines/azure-vm-watch |
| Configure Azure Event Hubs as a sink for VM watch signals | https://learn.microsoft.com/en-us/azure/virtual-machines/configure-eventhub-vm-watch |
| Customize VM watch settings and collectors on Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/configure-vm-watch |
| Configure and create Azure Compute Galleries | https://learn.microsoft.com/en-us/azure/virtual-machines/create-gallery |
| Configure custom data for Azure virtual machines | https://learn.microsoft.com/en-us/azure/virtual-machines/custom-data |
| Convert Azure managed disk types via CLI, PowerShell, portal | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-convert-types |
| Deploy zone-redundant managed disks (ZRS) | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-deploy-zrs |
| Enable on-demand bursting for Premium SSD disks | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-enable-bursting |
| Configure and deploy Azure Ultra Disks for VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-enable-ultra-ssd |
| Instantly access Azure managed disk snapshots | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-instant-access-snapshots |
| Use Azure disk metrics and bursting metrics | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-metrics |
| Convert managed disks from LRS to ZRS redundancy | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-migrate-lrs-zrs |
| Change performance tiers for Azure Managed Disks | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-performance-tiers |
| Enable and configure Azure shared managed disks | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-shared-enable |
| Configure torn-write prevention on Linux managed disks | https://learn.microsoft.com/en-us/azure/virtual-machines/disks-torn-write-prevention |
| Check supported OS images for Azure NVMe | https://learn.microsoft.com/en-us/azure/virtual-machines/enable-nvme-interface |
| Configure Azure Monitor Dependency agent extension for Linux | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/agent-dependency-linux |
| Configure Azure Monitor Dependency agent extension for Windows | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/agent-dependency-windows |
| Configure and manage Azure Linux VM Agent settings | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/agent-linux |
| Install and manage Azure Windows VM Agent | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/agent-windows |
| Configure Chef VM Extension on Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/chef |
| Configure Custom Script Extension v2 on Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/custom-script-linux |
| Configure Custom Script Extension on Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/custom-script-windows |
| Overview and configuration of DSC extension for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/dsc-overview |
| Author ARM templates for Azure DSC VM extension | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/dsc-template |
| Configure Azure DSC Extension on Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/dsc-windows |
| Configure and enable InfiniBand on Azure HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/enable-infiniband |
| Configure Machine Configuration extension for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/guest-configuration |
| Configure Application Health extension for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/health-extension |
| Configure InfiniBand driver extension on Linux HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpc-compute-infiniband-linux |
| Configure InfiniBand driver extension on Windows HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpc-compute-infiniband-windows |
| Configure AMD GPU Driver Extension on Linux N-series VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpccompute-amd-gpu-linux |
| Configure AMD GPU Driver Extension on Windows NVv4 VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpccompute-amd-gpu-windows |
| Configure NVIDIA GPU Driver Extension on Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpccompute-gpu-linux |
| Configure NVIDIA GPU Driver Extension on Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/hpccompute-gpu-windows |
| Configure Microsoft Antimalware Extension for Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/iaas-antimalware-windows |
| Configure Azure Key Vault VM extension on Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/key-vault-linux |
| Configure Azure Key Vault VM extension on Windows | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/key-vault-windows |
| Configure Qualys Cloud Agent extension on Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/qualys |
| Configure Salt Minion VM Extension for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/salt-minion |
| Configure Stackify Retrace Linux agent extension on Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/stackify-retrace-linux |
| Configure Tenable One-Click Nessus VM Extension | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/tenable |
| Use VMAccess extension to reset Linux VM access | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/vmaccess-linux |
| Use VMAccess extension to reset Windows VM access | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/vmaccess-windows |
| Configure VM Snapshot Linux extension for Azure Backup | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/vmsnapshot-linux |
| Configure VM Snapshot Windows extension for Azure Backup | https://learn.microsoft.com/en-us/azure/virtual-machines/extensions/vmsnapshot-windows |
| Use Azure FPGA Attestation service for NP-series VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/field-programmable-gate-arrays-attestation |
| Configure Azure Monitor VM availability metric with Flash | https://learn.microsoft.com/en-us/azure/virtual-machines/flash-azure-monitor |
| Enable and configure Azure Write Accelerator | https://learn.microsoft.com/en-us/azure/virtual-machines/how-to-enable-write-accelerator |
| Understand HX-series VM architecture and topology | https://learn.microsoft.com/en-us/azure/virtual-machines/hx-series-overview |
| Install Azure VM watch via ARM, PowerShell, or CLI | https://learn.microsoft.com/en-us/azure/virtual-machines/install-vm-watch |
| Attach persistent data disks to Linux VMs using CLI | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/add-disk |
| Attach new or existing data disks to Linux VMs in portal | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/attach-disk-portal |
| Install AMD GPU drivers on Azure N-series Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/azure-n-series-amd-gpu-driver-linux-installation-guide |
| Create and upload CentOS-based VHDs to Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/create-upload-centos |
| Prepare generic Linux systems for Azure imaging | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/create-upload-generic |
| Create and upload OpenBSD images for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/create-upload-openbsd |
| Prepare Debian Linux VHD images for Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/debian-create-upload-vhd |
| Use Flatcar Container Linux VHDs in Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/flatcar-create-upload-vhd |
| Configure Azure VM Image Builder with Compute Gallery | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/image-builder |
| Author Bicep and ARM templates for Azure Image Builder | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/image-builder-json |
| Configure networking for Azure VM Image Builder | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/image-builder-networking |
| Configure NVIDIA GPU drivers on Linux N-series VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/n-series-driver-setup |
| Create and upload Oracle Linux VHDs to Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/oracle-create-upload-vhd |
| Understand Linux VM provisioning parameters in Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/provisioning |
| Prepare and upload RHEL VHDs for Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/redhat-create-upload-vhd |
| Use Run Command to execute scripts on Linux Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/run-command |
| Configure managed Run Command for Linux Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/run-command-managed |
| Create and upload SUSE Linux VHDs in Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/suse-create-upload-vhd |
| Configure time synchronization for Azure Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/time-sync |
| Configure xrdp and desktop environment on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/linux/use-remote-desktop |
| Control Azure VM platform updates with Maintenance Configurations | https://learn.microsoft.com/en-us/azure/virtual-machines/maintenance-configurations |
| Define Maintenance Configurations for Azure VMs using Bicep | https://learn.microsoft.com/en-us/azure/virtual-machines/maintenance-configurations-bicep |
| Manage Azure VM Maintenance Configurations using Azure CLI | https://learn.microsoft.com/en-us/azure/virtual-machines/maintenance-configurations-cli |
| Configure Azure VM Maintenance Configurations in the portal | https://learn.microsoft.com/en-us/azure/virtual-machines/maintenance-configurations-portal |
| Configure Maintenance Configurations for dedicated hosts with PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machines/maintenance-configurations-powershell |
| Manage and restore Azure VMs from restore points | https://learn.microsoft.com/en-us/azure/virtual-machines/manage-restore-points |
| Export Compute Gallery image versions to managed disks | https://learn.microsoft.com/en-us/azure/virtual-machines/managed-disk-from-image-version |
| Configure Marketplace purchase plans for gallery images | https://learn.microsoft.com/en-us/azure/virtual-machines/marketplace-images |
| Reference monitoring data for Azure Virtual Machines | https://learn.microsoft.com/en-us/azure/virtual-machines/monitor-vm-reference |
| Convert Azure Linux VM disks from SCSI to NVMe | https://learn.microsoft.com/en-us/azure/virtual-machines/nvme-linux |
| Configure and enable NVMe on Azure virtual machines | https://learn.microsoft.com/en-us/azure/virtual-machines/nvme-overview |
| Configure InfiniBand networking on Azure HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/setup-infiniband |
| Configure MPI for RDMA-enabled Azure HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/setup-mpi |
| Configure MPI for RDMA-capable Azure HPC VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/setup-mpi |
| Create and store SSH keys with Azure CLI | https://learn.microsoft.com/en-us/azure/virtual-machines/ssh-keys-azure-cli |
| Configure and manage SSH keys in Azure portal | https://learn.microsoft.com/en-us/azure/virtual-machines/ssh-keys-portal |
| List, update, and delete Compute Gallery resources | https://learn.microsoft.com/en-us/azure/virtual-machines/update-image-resources |
| Configure user data scripts for Azure VMs at provisioning | https://learn.microsoft.com/en-us/azure/virtual-machines/user-data |
| Control OS image upgrades on VM scale sets with Maintenance control | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machine-scale-sets-maintenance-control |
| Use Azure CLI to manage Maintenance control for VM scale set OS upgrades | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machine-scale-sets-maintenance-control-cli |
| Configure Maintenance control for VM scale set OS upgrades in the portal | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machine-scale-sets-maintenance-control-portal |
| Use PowerShell to manage Maintenance control for VM scale set OS upgrades | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machine-scale-sets-maintenance-control-powershell |
| Define Maintenance control for VM scale sets using ARM templates | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machine-scale-sets-maintenance-control-template |
| Create Azure VM restore points using PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machines-create-restore-points-powershell |
| Configure cross-region copy of Azure VM restore points | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machines-restore-points-copy |
| Configure VM Snapshot extension for restore points | https://learn.microsoft.com/en-us/azure/virtual-machines/virtual-machines-restore-points-vm-snapshot-extension |
| Configure VM watch Collectors Suite for Azure VM health checks | https://learn.microsoft.com/en-us/azure/virtual-machines/vm-watch-collector-suite |
| Attach data disks to Windows VMs using PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/attach-disk-ps |
| Attach managed data disks to Windows VMs in portal | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/attach-managed-disk-portal |
| Find Marketplace image URNs and plans with PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/cli-ps-findimage |
| Configure WinRM connectivity for Azure Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/connect-winrm |
| Configure Azure Diagnostics Extension for Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/extensions-diagnostics |
| Set up time sync for AD domain Windows VMs in Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/external-ntpsource-configuration |
| Configure AMD GPU drivers on Azure N-series Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/n-series-amd-driver-setup |
| Install NVIDIA GPU drivers on Windows N-series VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/n-series-driver-setup |
| Use Run Command to execute scripts on Windows Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/run-command |
| Configure managed Run Command for Windows Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/run-command-managed |
| Define Azure VM resources in ARM templates | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/template-description |
| Configure time synchronization for Azure Windows VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/windows/time-sync |
| Configure ExpressRoute and OCI FastConnect for Oracle apps | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/configure-azure-oci-networking |
| Install and configure Oracle ASM on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/configure-oracle-asm |
| Configure Oracle Data Guard on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/configure-oracle-dataguard |
| Install and configure Oracle GoldenGate on Azure VMs | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/configure-oracle-golden-gate |
| Back up Oracle Database on Azure VMs using Azure Backup | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/oracle-database-backup-azure-backup |
| Back up Oracle Database to Azure Files with RMAN | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/oracle/oracle-database-backup-azure-storage |
| Use Red Hat Update Infrastructure for RHEL on Azure | https://learn.microsoft.com/en-us/azure/virtual-machines/workloads/redhat/redhat-rhui |

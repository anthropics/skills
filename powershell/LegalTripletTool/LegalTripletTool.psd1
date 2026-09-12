@{
    RootModule        = 'LegalTripletTool.psm1'
    ModuleVersion     = '0.3.0'
    GUID              = 'd6efe1de-7d0b-4fc0-a3d4-1fbc7ccde582'
    Author            = 'Codex'
    CompanyName       = 'Independent'
    Copyright         = '(c) Codex'
    Description       = 'Triplet-oriented legal document ingestion/search module for JSON/XML/PDF link workflows, seed-link resolution, and control console prototype.'
    PowerShellVersion = '7.0'
    FunctionsToExport = @(
        'Get-LegalObjectCollection',
        'ConvertTo-LegalTripletSet',
        'Resolve-LegalSeedLinks',
        'Search-LegalTriplets',
        'Merge-LegalObjectsUnifiedOutput',
        'Export-LegalUnifiedOutput',
        'Start-ComputerControlConsole',
        'Build-EvidenceSourceXml'
    )
    PrivateData = @{
        PSData = @{
            Tags       = @('legal', 'triplet', 'xml', 'json', 'pdf', 'search', 'seed-linking')
            ProjectUri = 'https://example.local/LegalTripletTool'
        }
    }
}

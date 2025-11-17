# ==============================================================================
# Reflections Module - Simple CSV Tail + JSON Reflection Writer
# Model reads CSV tail, writes reflection JSON, returns it
# ==============================================================================

# ==============================================================================
# Initialize Reflection Store
# ==============================================================================

function Initialize-ReflectionStore {
    param(
        [string]$BasePath = (Join-Path $PSScriptRoot 'shared_bus')
    )

    $dirs = @(
        'inbox',
        'outbox',
        'reflections',
        'logs'
    )

    foreach ($dir in $dirs) {
        $fullPath = Join-Path $BasePath $dir
        if (-not (Test-Path $fullPath)) {
            New-Item -ItemType Directory -Path $fullPath -Force | Out-Null
            Write-Verbose "[REFLECT] Created directory: $fullPath"
        }
    }

    # Initialize CSV log if it doesn't exist
    $csvPath = Join-Path $BasePath 'logs\hub_events.csv'
    if (-not (Test-Path $csvPath)) {
        $header = @(
            'epoch_ms',
            'type',
            'source_model',
            'action',
            'uid',
            'content_preview',
            'meta_tags',
            'detail_path'
        )
        $header -join ',' | Out-File $csvPath -Encoding UTF8
        Write-Verbose "[REFLECT] Initialized CSV: $csvPath"
    }

    return @{
        base = $BasePath
        inbox = Join-Path $BasePath 'inbox'
        outbox = Join-Path $BasePath 'outbox'
        reflections = Join-Path $BasePath 'reflections'
        logs = Join-Path $BasePath 'logs'
        csv = $csvPath
    }
}

# ==============================================================================
# Add Log Row to CSV
# ==============================================================================

function Add-LogRow {
    param(
        [Parameter(Mandatory=$true)]
        [string]$Type,

        [Parameter(Mandatory=$false)]
        [string]$SourceModel = '',

        [Parameter(Mandatory=$false)]
        [string]$Action = '',

        [Parameter(Mandatory=$false)]
        [string]$Uid = '',

        [Parameter(Mandatory=$false)]
        [string]$ContentPreview = '',

        [Parameter(Mandatory=$false)]
        [string]$MetaTags = '',

        [Parameter(Mandatory=$false)]
        [string]$DetailPath = '',

        [Parameter(Mandatory=$false)]
        [string]$CsvPath = $null
    )

    if (-not $CsvPath) {
        $store = Initialize-ReflectionStore
        $CsvPath = $store.csv
    }

    $epochMs = [DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds()

    # Escape CSV fields
    $escapeCsv = {
        param($str)
        if ($str -match '[",\n\r]') {
            return "`"$($str -replace '"', '""')`""
        }
        return $str
    }

    $row = @(
        $epochMs,
        (& $escapeCsv $Type),
        (& $escapeCsv $SourceModel),
        (& $escapeCsv $Action),
        (& $escapeCsv $Uid),
        (& $escapeCsv $ContentPreview),
        (& $escapeCsv $MetaTags),
        (& $escapeCsv $DetailPath)
    ) -join ','

    Add-Content -Path $CsvPath -Value $row -Encoding UTF8

    return @{
        epoch_ms = $epochMs
        type = $Type
        source_model = $SourceModel
        action = $Action
        uid = $Uid
        content_preview = $ContentPreview
        meta_tags = $MetaTags
        detail_path = $DetailPath
    }
}

# ==============================================================================
# Get CSV Tail (Last N Rows)
# ==============================================================================

function Get-LogTailCsv {
    param(
        [Parameter(Mandatory=$false)]
        [int]$Count = 30,

        [Parameter(Mandatory=$false)]
        [string]$CsvPath = $null
    )

    if (-not $CsvPath) {
        $store = Initialize-ReflectionStore
        $CsvPath = $store.csv
    }

    if (-not (Test-Path $CsvPath)) {
        return @{
            ok = $true
            rows = @()
            count = 0
        }
    }

    try {
        $lines = Get-Content -Path $CsvPath -Encoding UTF8 -ErrorAction Stop

        if ($lines.Count -le 1) {
            return @{
                ok = $true
                rows = @()
                count = 0
            }
        }

        # Get header
        $header = $lines[0] -split ','

        # Get last N data rows
        $dataLines = $lines[1..($lines.Count - 1)]
        $startIndex = [Math]::Max(0, $dataLines.Count - $Count)
        $tailLines = $dataLines[$startIndex..($dataLines.Count - 1)]

        # Parse rows
        $rows = @()
        foreach ($line in $tailLines) {
            if (-not $line) { continue }

            # Simple CSV parse (handles quoted fields)
            $fields = @()
            $inQuote = $false
            $current = ''

            for ($i = 0; $i -lt $line.Length; $i++) {
                $char = $line[$i]

                if ($char -eq '"') {
                    if ($inQuote -and $i+1 -lt $line.Length -and $line[$i+1] -eq '"') {
                        $current += '"'
                        $i++
                    } else {
                        $inQuote = -not $inQuote
                    }
                } elseif ($char -eq ',' -and -not $inQuote) {
                    $fields += $current
                    $current = ''
                } else {
                    $current += $char
                }
            }
            $fields += $current

            # Create row object
            $row = @{}
            for ($j = 0; $j -lt [Math]::Min($header.Count, $fields.Count); $j++) {
                $row[$header[$j]] = $fields[$j]
            }
            $rows += $row
        }

        return @{
            ok = $true
            rows = $rows
            count = $rows.Count
        }
    } catch {
        return @{
            ok = $false
            error = $_.Exception.Message
        }
    }
}

# ==============================================================================
# Request Reflection Window (CSV Tail Packaged for Model)
# ==============================================================================

function Request-ReflectionWindow {
    param(
        [Parameter(Mandatory=$false)]
        [int]$RowCount = 30
    )

    $tail = Get-LogTailCsv -Count $RowCount

    $requestId = [guid]::NewGuid().ToString()

    return @{
        ok = $tail.ok
        request_id = $requestId
        window = @{
            row_count = $tail.count
            window_rows = $tail.rows
        }
    }
}

# ==============================================================================
# Submit Reflection (Write JSON + CSV Row)
# ==============================================================================

function Submit-ReflectionRow {
    param(
        [Parameter(Mandatory=$true)]
        [hashtable]$Reflection,

        [Parameter(Mandatory=$false)]
        [string]$Uid = '',

        [Parameter(Mandatory=$false)]
        [string]$MetaTags = ''
    )

    $store = Initialize-ReflectionStore

    $epochMs = [DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds()

    # Write full reflection JSON
    $jsonFileName = "reflection_$epochMs.json"
    $jsonPath = Join-Path $store.reflections $jsonFileName

    $Reflection | ConvertTo-Json -Depth 10 | Out-File $jsonPath -Encoding UTF8

    # Extract preview
    $preview = if ($Reflection.title) {
        $Reflection.title.Substring(0, [Math]::Min(100, $Reflection.title.Length))
    } else {
        'Reflection'
    }

    # Add compact CSV row pointing to JSON
    $logRow = Add-LogRow -Type 'reflection' `
                         -SourceModel ($Reflection.source_model -or 'unknown') `
                         -Action 'submit' `
                         -Uid $Uid `
                         -ContentPreview $preview `
                         -MetaTags $MetaTags `
                         -DetailPath $jsonPath `
                         -CsvPath $store.csv

    return @{
        ok = $true
        epoch_ms = $epochMs
        json_path = $jsonPath
        csv_row = $logRow
    }
}

# ==============================================================================
# Write Event (Generic Event Logging)
# ==============================================================================

function Write-EventJsonl {
    param(
        [Parameter(Mandatory=$true)]
        [string]$Type,

        [Parameter(Mandatory=$false)]
        [string]$SourceModel = '',

        [Parameter(Mandatory=$false)]
        [string]$Action = '',

        [Parameter(Mandatory=$false)]
        [string]$Uid = '',

        [Parameter(Mandatory=$false)]
        [string]$Content = '',

        [Parameter(Mandatory=$false)]
        [string]$MetaTags = ''
    )

    # Just log to CSV (simpler than separate JSONL)
    $preview = if ($Content.Length -gt 100) {
        $Content.Substring(0, 100) + '...'
    } else {
        $Content
    }

    return Add-LogRow -Type $Type `
                      -SourceModel $SourceModel `
                      -Action $Action `
                      -Uid $Uid `
                      -ContentPreview $preview `
                      -MetaTags $MetaTags
}

# ==============================================================================
# Export Functions
# ==============================================================================

Export-ModuleMember -Function @(
    'Initialize-ReflectionStore',
    'Add-LogRow',
    'Get-LogTailCsv',
    'Request-ReflectionWindow',
    'Submit-ReflectionRow',
    'Write-EventJsonl'
)

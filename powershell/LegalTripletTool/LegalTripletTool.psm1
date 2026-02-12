Set-StrictMode -Version Latest

function Get-StringSimilarity {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [string]$A,
        [Parameter(Mandatory)] [string]$B
    )

    if ($A -eq $B) { return 1.0 }
    if ([string]::IsNullOrWhiteSpace($A) -or [string]::IsNullOrWhiteSpace($B)) { return 0.0 }

    $lenA = $A.Length
    $lenB = $B.Length
    $d = New-Object 'int[,]' ($lenA + 1), ($lenB + 1)

    for ($i = 0; $i -le $lenA; $i++) { $d[$i, 0] = $i }
    for ($j = 0; $j -le $lenB; $j++) { $d[0, $j] = $j }

    for ($i = 1; $i -le $lenA; $i++) {
        for ($j = 1; $j -le $lenB; $j++) {
            $cost = if ($A[$i - 1] -eq $B[$j - 1]) { 0 } else { 1 }
            $deletion = $d[$i - 1, $j] + 1
            $insertion = $d[$i, $j - 1] + 1
            $substitution = $d[$i - 1, $j - 1] + $cost
            $d[$i, $j] = [Math]::Min([Math]::Min($deletion, $insertion), $substitution)
        }
    }

    $distance = $d[$lenA, $lenB]
    $maxLen = [Math]::Max($lenA, $lenB)
    return [Math]::Round((1 - ($distance / $maxLen)), 4)
}

function Convert-XmlNodeToHashtable {
    [CmdletBinding()]
    param([Parameter(Mandatory)] [System.Xml.XmlNode]$Node)

    $attrs = @{}
    if ($Node.Attributes) {
        foreach ($attr in $Node.Attributes) {
            $attrs[$attr.Name] = $attr.Value
        }
    }

    $childElements = @($Node.ChildNodes | Where-Object { $_.NodeType -eq [System.Xml.XmlNodeType]::Element })
    if ($childElements.Count -eq 0) {
        $text = $Node.InnerText
        if ($attrs.Count -gt 0) {
            return @{
                _attributes = $attrs
                _text = $text
            }
        }

        return $text
    }

    $result = @{}
    if ($attrs.Count -gt 0) {
        $result['_attributes'] = $attrs
    }

    foreach ($child in $childElements) {
        $childValue = Convert-XmlNodeToHashtable -Node $child
        if ($result.ContainsKey($child.Name)) {
            if ($result[$child.Name] -isnot [System.Collections.IList]) {
                $result[$child.Name] = @($result[$child.Name])
            }
            $result[$child.Name] += $childValue
        } else {
            $result[$child.Name] = $childValue
        }
    }

    return $result
}

function Convert-ObjectToTriplets {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [object]$InputObject,
        [Parameter(Mandatory)] [string]$Subject,
        [string]$PathPrefix = '',
        [string[]]$AtomicPropertyNames = @('Triplet', 'Triplets', 'Temporal', 'Meta', 'notes', 'significance', 'description_long')
    )

    $triplets = New-Object System.Collections.Generic.List[object]

    function Add-TripletsRecursive {
        param(
            [object]$Value,
            [string]$CurrentPath
        )

        if ($null -eq $Value) {
            $triplets.Add([pscustomobject]@{ Subject = $Subject; Predicate = $CurrentPath; Object = $null; Type = 'null' })
            return
        }

        $leafName = if ($CurrentPath) { ($CurrentPath -split '[\.\[]')[-1] } else { '' }
        if ($leafName -and ($AtomicPropertyNames -contains $leafName)) {
            $triplets.Add([pscustomobject]@{
                Subject = $Subject
                Predicate = $CurrentPath
                Object = ($Value | ConvertTo-Json -Depth 50 -Compress)
                Type = 'AtomicJson'
            })
            return
        }

        if ($Value -is [System.Collections.IDictionary]) {
            foreach ($k in $Value.Keys) {
                $childPath = if ($CurrentPath) { "$CurrentPath.$k" } else { [string]$k }
                Add-TripletsRecursive -Value $Value[$k] -CurrentPath $childPath
            }
            return
        }

        if ($Value -is [pscustomobject]) {
            $props = $Value.PSObject.Properties
            if ($props.Count -eq 0) {
                $triplets.Add([pscustomobject]@{ Subject = $Subject; Predicate = $CurrentPath; Object = [string]$Value; Type = 'String' })
                return
            }

            foreach ($prop in $props) {
                $childPath = if ($CurrentPath) { "$CurrentPath.$($prop.Name)" } else { $prop.Name }
                Add-TripletsRecursive -Value $prop.Value -CurrentPath $childPath
            }
            return
        }

        if ($Value -is [System.Collections.IEnumerable] -and $Value -isnot [string]) {
            $idx = 0
            foreach ($item in $Value) {
                $childPath = "$CurrentPath[$idx]"
                Add-TripletsRecursive -Value $item -CurrentPath $childPath
                $idx++
            }
            return
        }

        $typeName = $Value.GetType().Name
        $triplets.Add([pscustomobject]@{ Subject = $Subject; Predicate = $CurrentPath; Object = [string]$Value; Type = $typeName })
    }

    Add-TripletsRecursive -Value $InputObject -CurrentPath $PathPrefix
    return $triplets
}

function Get-LegalObjectCollection {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [string[]]$Path,
        [switch]$Recurse,
        [int]$LinkThresholdChars = 150000,
        [switch]$AttemptPdfText,
        [string[]]$NoSplitProperties = @('Triplet', 'Temporal', 'Meta')
    )

    $files = foreach ($p in $Path) {
        if (Test-Path $p -PathType Container) {
            Get-ChildItem -Path $p -File -Recurse:$Recurse
        } else {
            Get-Item -Path $p
        }
    }

    $collection = foreach ($file in $files) {
        $ext = $file.Extension.ToLowerInvariant()
        $base = [ordered]@{
            Id = [guid]::NewGuid().ToString()
            Name = $file.Name
            Path = $file.FullName
            Extension = $ext
            LastWriteTimeUtc = $file.LastWriteTimeUtc
            ContentType = 'link'
            Content = $null
            NoSplitProperties = $NoSplitProperties
        }

        switch ($ext) {
            '.json' {
                $raw = Get-Content -Raw -Path $file.FullName
                if ($raw.Length -gt $LinkThresholdChars) {
                    $base.ContentType = 'link'
                    $base.Content = @{ Link = $file.FullName; Reason = 'SizeThresholdExceeded' }
                } else {
                    $base.ContentType = 'json'
                    $base.Content = $raw | ConvertFrom-Json -Depth 100
                }
            }
            '.xml' {
                $raw = Get-Content -Raw -Path $file.FullName
                if ($raw.Length -gt $LinkThresholdChars) {
                    $base.ContentType = 'link'
                    $base.Content = @{ Link = $file.FullName; Reason = 'SizeThresholdExceeded' }
                } else {
                    [xml]$xmlDoc = $raw
                    $root = if ($xmlDoc.DocumentElement) { $xmlDoc.DocumentElement } else { $xmlDoc }
                    $base.ContentType = 'xml'
                    $base.Content = Convert-XmlNodeToHashtable -Node $root
                }
            }
            '.pdf' {
                if ($AttemptPdfText -and (Get-Command pdftotext -ErrorAction SilentlyContinue)) {
                    $tempFile = [System.IO.Path]::GetTempFileName()
                    & pdftotext -q "$($file.FullName)" "$tempFile"
                    $text = Get-Content -Raw -Path $tempFile
                    Remove-Item $tempFile -Force -ErrorAction SilentlyContinue
                    if ($text.Length -gt $LinkThresholdChars) {
                        $base.ContentType = 'link'
                        $base.Content = @{ Link = $file.FullName; Reason = 'PdfExtractTooLarge' }
                    } else {
                        $base.ContentType = 'pdf-text'
                        $base.Content = $text
                    }
                } else {
                    $base.ContentType = 'pdf-link'
                    $base.Content = @{ Link = $file.FullName; Reason = 'NoPdfExtractorEnabled' }
                }
            }
            default {
                $base.ContentType = 'link'
                $base.Content = @{ Link = $file.FullName; Reason = 'UnsupportedExtension' }
            }
        }

        [pscustomobject]$base
    }

    return $collection
}

function ConvertTo-LegalTripletSet {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory, ValueFromPipeline)] [object[]]$Collection,
        [switch]$IncludeLinks
    )

    begin {
        $allTriplets = New-Object System.Collections.Generic.List[object]
    }
    process {
        foreach ($item in $Collection) {
            $subject = if ($item.Id) { $item.Id } else { $item.Path }
            if ($item.ContentType -in @('json', 'xml')) {
                $atomic = if ($item.NoSplitProperties) { $item.NoSplitProperties } else { @() }
                $triplets = Convert-ObjectToTriplets -InputObject $item.Content -Subject $subject -PathPrefix $item.Name -AtomicPropertyNames $atomic
                foreach ($t in $triplets) { $allTriplets.Add($t) }
            } elseif ($IncludeLinks) {
                $allTriplets.Add([pscustomobject]@{
                    Subject = $subject
                    Predicate = 'link'
                    Object = $item.Path
                    Type = $item.ContentType
                })
            }
        }
    }
    end {
        return $allTriplets
    }
}

function Resolve-LegalSeedLinks {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [object[]]$Collection,
        [string]$XmlFactPath = 'MasterFacts.Facts.Fact',
        [string]$XmlFactIdProperty = '_attributes.id',
        [string]$JsonArgIdProperty = 'arg_id',
        [string]$JsonSeedArgIdProperty = 'seed_arg_id'
    )

    $facts = New-Object System.Collections.Generic.List[object]
    $responses = New-Object System.Collections.Generic.List[object]

    foreach ($item in $Collection) {
        if ($item.ContentType -eq 'xml') {
            $root = $item.Content
            if ($root.MasterFacts -and $root.MasterFacts.Facts -and $root.MasterFacts.Facts.Fact) {
                $f = $root.MasterFacts.Facts.Fact
                if ($f -is [System.Collections.IEnumerable] -and $f -isnot [string]) {
                    foreach ($entry in $f) {
                        $facts.Add([pscustomobject]@{
                            FactId = $entry._attributes.id
                            File = $item.Path
                            Statement = $entry.Statement
                            SourceKind = 'XMLFact'
                        })
                    }
                } else {
                    $facts.Add([pscustomobject]@{
                        FactId = $f._attributes.id
                        File = $item.Path
                        Statement = $f.Statement
                        SourceKind = 'XMLFact'
                    })
                }
            }
        }

        if ($item.ContentType -eq 'json') {
            $data = $item.Content
            if ($data -is [System.Collections.IEnumerable] -and $data -isnot [string]) {
                foreach ($entry in $data) {
                    $responses.Add([pscustomobject]@{
                        ArgId = $entry.arg_id
                        SeedArgId = $entry.seed_arg_id
                        TempFactId = $entry.temp_fact_id
                        File = $item.Path
                        DescriptionShort = $entry.description_short
                        SourceKind = 'JSONResponse'
                    })
                }
            }
        }
    }

    $links = foreach ($fact in $facts) {
        $direct = @($responses | Where-Object { $_.ArgId -eq $fact.FactId })
        $seed = @($responses | Where-Object {
            if ($_.SeedArgId) {
                ($_.SeedArgId -split '/') -contains $fact.FactId
            } else { $false }
        })

        [pscustomobject]@{
            FactId = $fact.FactId
            FactStatement = $fact.Statement
            FactFile = $fact.File
            DirectMatches = $direct
            SeedMatches = $seed
            DirectMatchCount = $direct.Count
            SeedMatchCount = $seed.Count
        }
    }

    [pscustomobject]@{
        GeneratedUtc = [DateTime]::UtcNow
        FactCount = $facts.Count
        ResponseCount = $responses.Count
        Links = $links
    }
}

function Search-LegalTriplets {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [object[]]$Triplets,
        [Parameter(Mandatory)] [string]$Query,
        [ValidateSet('Exact', 'Fuzzy', 'Backoff')] [string]$Mode = 'Exact',
        [double]$MinimumSimilarity = 0.75,
        [int]$MaxMatches = 100
    )

    $results = New-Object System.Collections.Generic.List[object]

    switch ($Mode) {
        'Exact' {
            foreach ($t in $Triplets) {
                $hay = "$($t.Subject) $($t.Predicate) $($t.Object)"
                if ($hay -match [regex]::Escape($Query)) {
                    $results.Add([pscustomobject]@{ Score = 1.0; MatchType = 'Exact'; Triplet = $t })
                }
            }
        }
        'Fuzzy' {
            foreach ($t in $Triplets) {
                $hay = "$($t.Subject) $($t.Predicate) $($t.Object)"
                $score = Get-StringSimilarity -A $Query.ToLowerInvariant() -B $hay.ToLowerInvariant()
                if ($score -ge $MinimumSimilarity) {
                    $results.Add([pscustomobject]@{ Score = $score; MatchType = 'Fuzzy'; Triplet = $t })
                }
            }
        }
        'Backoff' {
            $parts = $Query -split '\s+'
            for ($len = $parts.Count; $len -ge 1; $len--) {
                $candidate = ($parts[0..($len - 1)] -join ' ')
                foreach ($t in $Triplets) {
                    $hay = "$($t.Subject) $($t.Predicate) $($t.Object)"
                    if ($hay -match [regex]::Escape($candidate)) {
                        $score = [Math]::Round($len / $parts.Count, 4)
                        $results.Add([pscustomobject]@{ Score = $score; MatchType = "Backoff:$len"; Triplet = $t })
                    }
                }
                if ($results.Count -ge $MaxMatches) { break }
            }
        }
    }

    return $results | Sort-Object Score -Descending | Select-Object -First $MaxMatches
}

function Merge-LegalObjectsUnifiedOutput {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [object[]]$Collection,
        [double]$BranchSimilarity = 0.92,
        [switch]$AskBeforeRemoval
    )

    $groups = @()
    foreach ($item in $Collection) {
        $key = if ($item.Name) { $item.Name } else { [System.IO.Path]::GetFileName($item.Path) }
        $placed = $false

        foreach ($group in $groups) {
            $sim = Get-StringSimilarity -A $key.ToLowerInvariant() -B $group.Key.ToLowerInvariant()
            if ($sim -ge $BranchSimilarity) {
                $group.Items.Add($item)
                $placed = $true
                break
            }
        }

        if (-not $placed) {
            $groups += [pscustomobject]@{
                Key = $key
                Items = New-Object System.Collections.Generic.List[object]
            }
            $groups[-1].Items.Add($item)
        }
    }

    $output = [ordered]@{
        GeneratedUtc = [DateTime]::UtcNow
        GroupCount = $groups.Count
        Branches = @()
    }

    foreach ($group in $groups) {
        $branch = [ordered]@{
            BranchKey = $group.Key
            Variants = @($group.Items)
        }

        if ($AskBeforeRemoval) {
            $answer = Read-Host "Keep branch '$($group.Key)' with $($group.Items.Count) item(s)? [Y/n]"
            if ($answer -match '^(n|no)$') {
                continue
            }
        }

        $output.Branches += $branch
    }

    return [pscustomobject]$output
}

function Export-LegalUnifiedOutput {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [object]$UnifiedOutput,
        [Parameter(Mandatory)] [string]$Path
    )

    $json = $UnifiedOutput | ConvertTo-Json -Depth 100
    Set-Content -Path $Path -Value $json -Encoding UTF8
    Get-Item -Path $Path
}

function Convert-ButtonMapToPlaceholders {
    [CmdletBinding()]
    param([object[]]$Buttons)

    $out = New-Object System.Collections.Generic.List[object]
    $i = 1
    foreach ($b in $Buttons) {
        $name = if ($b.name) { $b.name } elseif ($b.label) { $b.label } else { "button_$i" }
        $x = if ($null -ne $b.x) { [int]$b.x } elseif ($b.centerX) { [int]$b.centerX } else { 0 }
        $y = if ($null -ne $b.y) { [int]$b.y } elseif ($b.centerY) { [int]$b.centerY } else { 0 }
        $out.Add([pscustomobject]@{
            Placeholder = "BTN_$i"
            Name = $name
            X = $x
            Y = $y
            Width = if ($b.width) { [int]$b.width } else { $null }
            Height = if ($b.height) { [int]$b.height } else { $null }
        })
        $i++
    }

    return $out
}

function Invoke-ConsoleAction {
    [CmdletBinding()]
    param([object]$Action)

    Add-Type -AssemblyName System.Windows.Forms
    Add-Type -AssemblyName System.Drawing

    if (-not $Action -or -not $Action.type) { return }

    switch ($Action.type.ToLowerInvariant()) {
        'mousemove' {
            [System.Windows.Forms.Cursor]::Position = [System.Drawing.Point]::new([int]$Action.x, [int]$Action.y)
        }
        'click' {
            [System.Windows.Forms.Cursor]::Position = [System.Drawing.Point]::new([int]$Action.x, [int]$Action.y)
            Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
public static class MouseInput {
  [DllImport("user32.dll")] public static extern void mouse_event(uint dwFlags, uint dx, uint dy, uint dwData, UIntPtr dwExtraInfo);
}
"@
            [MouseInput]::mouse_event(0x0002, 0, 0, 0, [UIntPtr]::Zero)
            [MouseInput]::mouse_event(0x0004, 0, 0, 0, [UIntPtr]::Zero)
        }
        'sendkeys' {
            [System.Windows.Forms.SendKeys]::SendWait([string]$Action.keys)
        }
    }
}

function Start-ComputerControlConsole {
    [CmdletBinding()]
    param(
        [Parameter(Mandatory)] [string]$OutputDir,
        [string]$ButtonMapPath,
        [string]$ModelEndpoint = 'http://localhost:11434/api/generate',
        [string]$ModelName = 'local-gguf',
        [int]$IntervalSeconds = 1,
        [switch]$EnableStreaming,
        [switch]$EnableInputControl
    )

    Add-Type -AssemblyName System.Drawing
    Add-Type -AssemblyName System.Windows.Forms

    if (-not (Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir | Out-Null
    }

    $buttonMapRaw = @()
    if ($ButtonMapPath -and (Test-Path $ButtonMapPath)) {
        $buttonMapRaw = Get-Content -Raw -Path $ButtonMapPath | ConvertFrom-Json -Depth 100
    }
    $buttonMap = Convert-ButtonMapToPlaceholders -Buttons $buttonMapRaw

    $overlayContext = ''
    Write-Host "Starting control console. Press Ctrl+C to stop."

    while ($true) {
        $bounds = [System.Windows.Forms.Screen]::PrimaryScreen.Bounds
        $bmp = New-Object System.Drawing.Bitmap $bounds.Width, $bounds.Height
        $graphics = [System.Drawing.Graphics]::FromImage($bmp)
        $graphics.CopyFromScreen($bounds.Location, [System.Drawing.Point]::Empty, $bounds.Size)

        $pen = New-Object System.Drawing.Pen([System.Drawing.Color]::FromArgb(95, 0, 255, 0), 1)
        for ($x = 0; $x -lt $bounds.Width; $x += 100) { $graphics.DrawLine($pen, $x, 0, $x, $bounds.Height) }
        for ($y = 0; $y -lt $bounds.Height; $y += 100) { $graphics.DrawLine($pen, 0, $y, $bounds.Width, $y) }

        $mouse = [System.Windows.Forms.Control]::MousePosition
        $graphics.FillEllipse([System.Drawing.Brushes]::Red, $mouse.X - 5, $mouse.Y - 5, 10, 10)

        $stamp = Get-Date -Format 'yyyyMMdd_HHmmss_fff'
        $imgPath = Join-Path $OutputDir "frame_$stamp.png"
        $bmp.Save($imgPath, [System.Drawing.Imaging.ImageFormat]::Png)
        $graphics.Dispose(); $bmp.Dispose(); $pen.Dispose()

        $prompt = @"
Screen tick at $stamp.
Mouse=($($mouse.X),$($mouse.Y)).
ScreenshotPath=$imgPath
Button placeholders:
$($buttonMap | ConvertTo-Json -Depth 20 -Compress)
OverlayContext=$overlayContext
Return JSON with optional actions array. Example: {"actions":[{"type":"mousemove","x":100,"y":200},{"type":"click","x":100,"y":200},{"type":"sendkeys","keys":"^a"}]}
"@

        $payload = @{
            model = $ModelName
            stream = [bool]$EnableStreaming
            prompt = $prompt
        } | ConvertTo-Json -Depth 20

        try {
            $outFile = Join-Path $OutputDir "model_$stamp.jsonl"
            if ($EnableStreaming) {
                $response = Invoke-WebRequest -Uri $ModelEndpoint -Method Post -ContentType 'application/json' -Body $payload -TimeoutSec 120
                $response.Content | Set-Content -Path $outFile -Encoding UTF8

                $lines = ($response.Content -split "`n") | Where-Object { -not [string]::IsNullOrWhiteSpace($_) }
                $assembled = ''
                foreach ($line in $lines) {
                    $lineObj = $line | ConvertFrom-Json -Depth 100
                    if ($lineObj.response) { $assembled += $lineObj.response }
                    if ($lineObj.done -eq $true) { break }
                }
                $overlayContext = "model_response:$assembled"

                if ($EnableInputControl) {
                    try {
                        $actionDoc = $assembled | ConvertFrom-Json -Depth 100
                        if ($actionDoc.actions) {
                            foreach ($action in $actionDoc.actions) {
                                Invoke-ConsoleAction -Action $action
                            }
                        }
                    } catch {
                        # Keep raw text in overlay context when response isn't JSON.
                    }
                }
            } else {
                $response = Invoke-RestMethod -Uri $ModelEndpoint -Method Post -ContentType 'application/json' -Body $payload -TimeoutSec 120
                $response | ConvertTo-Json -Depth 100 | Set-Content -Path $outFile -Encoding UTF8
                $overlayContext = "model_response:$($response.response)"
            }
        } catch {
            $errFile = Join-Path $OutputDir "error_$stamp.log"
            $_ | Out-String | Set-Content -Path $errFile -Encoding UTF8
        }

        Start-Sleep -Seconds $IntervalSeconds
    }
}

Export-ModuleMember -Function @(
    'Get-LegalObjectCollection',
    'ConvertTo-LegalTripletSet',
    'Resolve-LegalSeedLinks',
    'Search-LegalTriplets',
    'Merge-LegalObjectsUnifiedOutput',
    'Export-LegalUnifiedOutput',
    'Start-ComputerControlConsole'
)

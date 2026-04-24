[CmdletBinding()]
param()

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

$root = Get-AIToolRoot

foreach ($link in Get-LinkDefinitions) {
    $linkName = [string]$link.name
    $target = Resolve-PathValue $link.target_path
    $category = [string]$link.category

    if ([string]::IsNullOrWhiteSpace($linkName) -or [string]::IsNullOrWhiteSpace($target) -or [string]::IsNullOrWhiteSpace($category)) {
        continue
    }

    if (-not (Test-ConfiguredPath $target)) {
        Write-Warning "Skipping $linkName because target does not exist: $target"
        continue
    }

    $linkRoot = Join-Path $root $category
    if (-not (Test-Path -LiteralPath $linkRoot)) {
        New-Item -ItemType Directory -Path $linkRoot | Out-Null
    }

    $linkPath = Join-Path $linkRoot $linkName

    if (Test-Path -LiteralPath $linkPath) {
        $existing = Get-Item -LiteralPath $linkPath -Force
        $existingTarget = $null
        if ($existing.PSObject.Properties.Name -contains "Target") {
            $existingTarget = @($existing.Target)[0]
        }

        if ($existingTarget -eq $target) {
            Write-Host "Link already correct: $linkName -> $target"
            continue
        }

        Write-Warning "Link path already exists and was left unchanged: $linkPath"
        continue
    }

    New-Item -ItemType Junction -Path $linkPath -Target $target | Out-Null
    Write-Host "Created link: $linkName -> $target"
}

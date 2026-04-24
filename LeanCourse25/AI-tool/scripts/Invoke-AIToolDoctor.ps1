[CmdletBinding()]
param()

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

$configPath = Get-AIToolConfigPath
$config = Get-AIToolConfig
$root = Get-AIToolRoot

Write-Host "AI-tool root: $root"
Write-Host "Config path : $configPath"
Write-Host ""

$rows = @()

foreach ($profile in @($config.lean_profiles)) {
    $rows += [pscustomobject]@{
        Name = [string]$profile.name
        Kind = "lean"
        ProjectPath = if (Test-ConfiguredPath $profile.project_path) { "ok" } else { "missing" }
        Workspace = "n/a"
        OpenGauss = if (Test-ConfiguredPath $profile.opengauss_runner) { "ok" } else { "missing" }
        Link = "n/a"
    }
}

foreach ($profile in @($config.evaluation_profiles)) {
    $rows += [pscustomobject]@{
        Name = [string]$profile.name
        Kind = "evaluation"
        ProjectPath = if (Test-ConfiguredPath $profile.repo_path) { "ok" } else { "missing" }
        Workspace = "n/a"
        OpenGauss = "n/a"
        Link = "n/a"
    }
}

$rows += [pscustomobject]@{
    Name = "thesis"
    Kind = "writing"
    ProjectPath = if (Test-ConfiguredPath $config.thesis.project_path) { "ok" } elseif ($config.thesis.project_path) { "missing" } else { "n/a" }
    Workspace = if (Test-ConfiguredPath $config.thesis.workspace_path) { "ok" } else { "missing" }
    OpenGauss = "n/a"
    Link = "n/a"
}

foreach ($link in Get-LinkDefinitions) {
    $linkRoot = Join-Path $root ([string]$link.category)
    $linkPath = Join-Path $linkRoot ([string]$link.name)

    $rows += [pscustomobject]@{
        Name = [string]$link.name
        Kind = "link"
        ProjectPath = if (Test-ConfiguredPath $link.target_path) { "ok" } elseif ($link.target_path) { "missing" } else { "n/a" }
        Workspace = "n/a"
        OpenGauss = "n/a"
        Link = if (Test-Path -LiteralPath $linkPath) { "ok" } else { "missing" }
    }
}

$rows | Format-Table -AutoSize

Write-Host ""
Write-Host "Recommended next steps:"
Write-Host "  1. Run Sync-AIToolLinks.ps1 if any required link is missing."
Write-Host "  2. Run OpenGauss-Project.cmd doctor for the default Lean profile."
Write-Host "  3. Set thesis.project_path in profiles.local.json if you create a thesis repo."

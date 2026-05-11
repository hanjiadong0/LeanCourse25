[CmdletBinding()]
param(
    [string]$Profile,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$ArgsList
)

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

function Add-ExecutableParentToPath {
    param(
        [Parameter(Mandatory = $true)]
        [string]$CommandName
    )

    $command = Get-Command $CommandName -ErrorAction SilentlyContinue | Select-Object -First 1
    if (-not $command) {
        return
    }

    $commandPath = $command.Source
    if (-not $commandPath) {
        $commandPath = $command.Path
    }

    if (-not $commandPath) {
        return
    }

    $commandDir = Split-Path -Parent $commandPath
    if (-not $commandDir) {
        return
    }

    $pathParts = @($env:PATH -split ';') | Where-Object { $_ }
    if ($pathParts -contains $commandDir) {
        return
    }

    $env:PATH = "$commandDir;$env:PATH"
}

$resolvedProfile = $null
if ($Profile) {
    try {
        $resolvedProfile = Get-LeanProfile -Name $Profile
    }
    catch {
        $ArgsList = @($Profile) + @($ArgsList)
        $Profile = $null
    }
}

$profile = if ($resolvedProfile) { $resolvedProfile } else { Get-LeanProfile -Name $Profile }
$projectPath = Resolve-PathValue $profile.project_path
$runnerPath = Resolve-PathValue $profile.opengauss_runner

if (-not (Test-ConfiguredPath $projectPath)) {
    throw "Lean project path does not exist: $projectPath"
}

if (-not (Test-ConfiguredPath $runnerPath)) {
    throw "OpenGauss runner does not exist: $runnerPath"
}

# Some managed Gauss child sessions re-check tool availability using PATH only.
# Prepend the discovered executable directories so rg/codex remain visible.
Add-ExecutableParentToPath -CommandName "rg"
Add-ExecutableParentToPath -CommandName "codex"

Push-Location -LiteralPath $projectPath
try {
    & $runnerPath @ArgsList
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}

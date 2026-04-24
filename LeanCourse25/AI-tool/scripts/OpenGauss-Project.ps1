[CmdletBinding()]
param(
    [string]$Profile,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$ArgsList
)

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

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

Push-Location -LiteralPath $projectPath
try {
    & $runnerPath @ArgsList
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}

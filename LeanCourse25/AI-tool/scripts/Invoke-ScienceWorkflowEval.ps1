[CmdletBinding()]
param(
    [string]$Profile,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$ArgsList
)

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

$profile = Get-EvaluationProfile -Name $Profile
$repoPath = Resolve-PathValue $profile.repo_path
$pythonModule = Resolve-PathValue $profile.python_module

if (-not (Test-ConfiguredPath $repoPath)) {
    throw "Evaluation repo path does not exist: $repoPath"
}

if (-not $pythonModule) {
    throw "Evaluation profile does not define python_module."
}

Push-Location -LiteralPath $repoPath
try {
    if (-not $ArgsList -or $ArgsList.Count -eq 0) {
        Write-Host "Examples:"
        Write-Host "  python -m cambagent_eval validate configs\\experiments\\baseline.json"
        Write-Host "  python -m cambagent_eval dry-run configs\\experiments\\baseline.json"
        exit 0
    }

    python -m $pythonModule @ArgsList
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}

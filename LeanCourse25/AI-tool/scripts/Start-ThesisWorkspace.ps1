[CmdletBinding()]
param()

. (Join-Path $PSScriptRoot "AITool.Common.ps1")

$profile = Get-ThesisProfile
$workspacePath = Resolve-PathValue $profile.workspace_path
$projectPath = Resolve-PathValue $profile.project_path

if (-not (Test-ConfiguredPath $workspacePath)) {
    throw "Thesis workspace path does not exist: $workspacePath"
}

Write-Host "Thesis workspace: $workspacePath"
if (Test-ConfiguredPath $projectPath) {
    Write-Host "Thesis repo      : $projectPath"
} else {
    Write-Host "Thesis repo      : not configured yet"
}

Write-Host ""
Write-Host "Prompt files:"
Get-ChildItem -LiteralPath (Join-Path $workspacePath "prompts") -File | ForEach-Object {
    Write-Host ("  - " + $_.Name)
}

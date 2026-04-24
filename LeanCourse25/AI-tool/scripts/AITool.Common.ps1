Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Get-AIToolRoot {
    return Split-Path -Parent $PSScriptRoot
}

function Get-RepoRoot {
    return Split-Path -Parent (Get-AIToolRoot)
}

function Get-AIToolConfigPath {
    param(
        [switch]$AllowExample
    )

    $root = Get-AIToolRoot
    $localPath = Join-Path $root "config\\profiles.local.json"
    if (Test-Path -LiteralPath $localPath) {
        return $localPath
    }

    if ($AllowExample) {
        $examplePath = Join-Path $root "config\\profiles.example.json"
        if (Test-Path -LiteralPath $examplePath) {
            return $examplePath
        }
    }

    throw "Could not find profiles.local.json under $root\\config."
}

function Get-AIToolConfig {
    param(
        [switch]$AllowExample
    )

    $configPath = Get-AIToolConfigPath -AllowExample:$AllowExample
    $raw = Get-Content -LiteralPath $configPath -Raw
    return $raw | ConvertFrom-Json
}

function Resolve-PathValue {
    param(
        [AllowNull()][string]$PathValue
    )

    if ([string]::IsNullOrWhiteSpace($PathValue)) {
        return $null
    }

    return [string]$PathValue
}

function Test-ConfiguredPath {
    param(
        [AllowNull()][string]$PathValue
    )

    $resolved = Resolve-PathValue $PathValue
    if (-not $resolved) {
        return $false
    }

    return Test-Path -LiteralPath $resolved
}

function Get-LeanProfile {
    param(
        [string]$Name
    )

    $config = Get-AIToolConfig
    $resolvedName = if ($Name) { $Name } else { [string]$config.default_lean_profile }
    $profile = $config.lean_profiles | Where-Object { $_.name -eq $resolvedName } | Select-Object -First 1
    if (-not $profile) {
        throw "Lean profile '$resolvedName' was not found."
    }

    return $profile
}

function Get-EvaluationProfile {
    param(
        [string]$Name
    )

    $config = Get-AIToolConfig
    $resolvedName = if ($Name) { $Name } else { [string]$config.default_evaluation_profile }
    $profile = $config.evaluation_profiles | Where-Object { $_.name -eq $resolvedName } | Select-Object -First 1
    if (-not $profile) {
        throw "Evaluation profile '$resolvedName' was not found."
    }

    return $profile
}

function Get-ThesisProfile {
    $config = Get-AIToolConfig
    if (-not $config.thesis) {
        throw "The config does not define a thesis section."
    }

    return $config.thesis
}

function Get-LinkDefinitions {
    $config = Get-AIToolConfig
    if (-not $config.links) {
        return @()
    }

    return @($config.links)
}

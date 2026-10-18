param([switch]$NoClean)
$ErrorActionPreference = 'Stop'
$proofRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$repositoryRoot = Split-Path -Parent $proofRoot
$portableBin = Join-Path $repositoryRoot '.tools/lean/lean-4.19.0-windows/bin'
if (Test-Path -LiteralPath (Join-Path $portableBin 'lake.exe')) {
    $env:PATH = $portableBin + ';' + $env:PATH
}
$lakeCommand = Get-Command lake -ErrorAction Stop
$logRoot = Join-Path $proofRoot 'logs'
New-Item -ItemType Directory -Path $logRoot -Force | Out-Null
Push-Location $proofRoot
try {
    $compilerVersion = (& lake env lean --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $compilerVersion -notmatch 'version 4\.19\.0,') {
        throw "The project requires Lean 4.19.0; observed: $compilerVersion"
    }
    $packageManagerVersion = (& lake --version | Out-String).Trim()
    $sourceDigest = (Get-FileHash -LiteralPath 'OQ14.lean' -Algorithm SHA256).Hash
    $manifestDigest = (Get-FileHash -LiteralPath 'lake-manifest.json' -Algorithm SHA256).Hash
    @(
        $compilerVersion,
        $packageManagerVersion,
        "Source SHA256: $sourceDigest",
        "Dependency manifest SHA256: $manifestDigest",
        'Mathlib revision: c44e0c8ee63ca166450922a373c7409c5d26b00b',
        'Source rebuild: root .lake/build removed; pinned dependency cache retained.'
    ) | Set-Content -LiteralPath (Join-Path $logRoot 'toolchain.txt')

    if (-not $NoClean) {
        $buildTarget = [IO.Path]::GetFullPath((Join-Path $proofRoot '.lake/build'))
        $projectPrefix = [IO.Path]::GetFullPath($proofRoot).TrimEnd('\','/') + [IO.Path]::DirectorySeparatorChar
        if (-not $buildTarget.StartsWith($projectPrefix, [StringComparison]::OrdinalIgnoreCase)) {
            throw 'Refusing to remove build files outside the Lean project.'
        }
        if (Test-Path -LiteralPath $buildTarget) {
            Remove-Item -LiteralPath $buildTarget -Recurse -Force
        }
    }

    $buildLogPath = Join-Path $logRoot 'clean-build.txt'
    & lake build OQ14 2>&1 | Tee-Object -FilePath $buildLogPath
    $compilerExit = $LASTEXITCODE
    "Compiler exit code: $compilerExit" | Add-Content -LiteralPath $buildLogPath
    if ($compilerExit -ne 0) { throw "Lean build failed with exit code $compilerExit" }

    $proofSource = Get-Content -LiteralPath 'OQ14.lean' -Raw
    $buildLog = Get-Content -LiteralPath $buildLogPath -Raw
    if ($proofSource -match '(?m)^\s*(axiom|constant)\s|\b(sorry|admit)\b') {
        throw 'A forbidden unproved declaration was found in the formal source.'
    }
    if ($buildLog -match 'sorryAx') {
        throw 'An admitted proof dependency was found in the compiler axiom report.'
    }
    'Source and axiom-report checks passed.' | Add-Content -LiteralPath $buildLogPath
    Write-Output 'Lean proof build and axiom audit passed.'
} finally {
    Pop-Location
}

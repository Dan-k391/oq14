param([switch]$NoClean, [string]$Python = 'python')
$ErrorActionPreference = 'Stop'
$proofRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$repositoryRoot = Split-Path -Parent $proofRoot
$proofBuildArguments = @(
    (Join-Path $proofRoot 'build.py'),
    '--log-dir', (Join-Path $repositoryRoot 'output/lean')
)
if ($NoClean) { $proofBuildArguments += '--no-clean' }
& $Python @proofBuildArguments
if ($LASTEXITCODE -ne 0) {
    throw "Combined Lean build and axiom audit failed with exit code $LASTEXITCODE"
}

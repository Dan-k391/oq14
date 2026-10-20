param([string[]]$RelativePaths = @())
$ErrorActionPreference = 'Stop'
$workspaceRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$savedRoot = Join-Path $PSScriptRoot 'work'
if ($RelativePaths.Count -eq 0) {
    Write-Output 'Supply one or more original relative paths, for example: -RelativePaths lean/NewtonConvolution.lean'
    exit 0
}
foreach ($relativePath in $RelativePaths) {
    $savedPath = [System.IO.Path]::GetFullPath((Join-Path $savedRoot $relativePath))
    $workingPath = [System.IO.Path]::GetFullPath((Join-Path $workspaceRoot $relativePath))
    if (-not $savedPath.StartsWith($savedRoot + [System.IO.Path]::DirectorySeparatorChar) -or
        -not $workingPath.StartsWith($workspaceRoot + [System.IO.Path]::DirectorySeparatorChar)) {
        throw 'Path must remain inside the checkpoint and workspace.'
    }
    if (Test-Path -LiteralPath $workingPath) { throw "Refusing to overwrite $workingPath" }
    if (-not (Test-Path -LiteralPath $savedPath -PathType Leaf)) { throw "Missing saved file $savedPath" }
    New-Item -ItemType Directory -Path ([System.IO.Path]::GetDirectoryName($workingPath)) -Force | Out-Null
    Copy-Item -LiteralPath $savedPath -Destination $workingPath
    Write-Output "Restored $relativePath"
}

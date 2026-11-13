$ErrorActionPreference='Stop'
$dest='D:/oq14/checkpoints/2026-11-13-flat-continuity/reviews'
$manifest=Get-Content -Raw 'D:/oq14/checkpoints/2026-11-12-full-closure/packet05-continuity-author-manifest.json' | ConvertFrom-Json
$env:LEAN_PATH="$dest/objects;$env:LEAN_PATH"
foreach($item in $manifest.modules) {
  $src="D:/oq14/lean/$($item.module).lean"
  $before=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
  if($before -ne $item.source_sha256){throw "Hash mismatch: $($item.module)"}
  & 'D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe' -o "$dest/objects/$($item.module).olean" $src *> "$dest/$($item.module).log"
  if($LASTEXITCODE -ne 0){throw "Build failed: $($item.module)"}
  $after=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
  if($after -ne $before){throw "Source changed: $($item.module)"}
  $log=Get-Content -Raw "$dest/$($item.module).log"
  if($log -match 'warning:|error:|sorryAx'){throw "Bad build report: $($item.module)"}
  foreach($report in $item.reports){if(-not $log.Contains("'$report' depends on axioms:")){throw "Missing report: $report"}}
}

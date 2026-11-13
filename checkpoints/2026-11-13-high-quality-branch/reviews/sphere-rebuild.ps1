$ErrorActionPreference='Stop'
$d='D:/oq14/checkpoints/2026-11-13-high-quality-branch/reviews'
$items=Get-Content -Raw "$d/sphere-inputs.json" | ConvertFrom-Json
$env:LEAN_PATH="$d/sphere-objects;$d/certified-objects;$d/objects;D:/oq14/checkpoints/2026-11-13-normalized-outgoing/reviews/pole-scale-objects;D:/oq14/checkpoints/2026-11-13-normalized-outgoing/reviews/objects;D:/oq14/checkpoints/2026-11-13-actual-mode-poles/reviews/extension-objects;D:/oq14/checkpoints/2026-11-13-actual-mode-poles/reviews/objects;$env:LEAN_PATH"
foreach($item in $items){
 $src="D:/oq14/lean/$($item.module).lean"
 $before=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
 if($before -ne $item.sha256){throw "source mismatch $($item.module)"}
 & 'D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe' -o "$d/sphere-objects/$($item.module).olean" $src *> "$d/sphere-$($item.module).log"
 if($LASTEXITCODE -ne 0){throw "compile failed $($item.module)"}
 $after=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
 if($after -ne $before){throw "source changed $($item.module)"}
 $log=Get-Content -Raw "$d/sphere-$($item.module).log"
 if($log -match 'warning:|error:|sorryAx'){throw "bad output $($item.module)"}
 foreach($report in $item.reports){if(-not $log.Contains("'$report' depends on axioms:")){throw "missing $report"}}
}

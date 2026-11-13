$ErrorActionPreference='Stop'
$d='D:/oq14/checkpoints/2026-11-13-actual-mode-poles/reviews'
$items=Get-Content -Raw "$d/inputs.json" | ConvertFrom-Json
$env:LEAN_PATH="$d/objects;$env:LEAN_PATH"
foreach($item in $items){
 $src="D:/oq14/lean/$($item.module).lean"
 $before=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
 if($before -ne $item.sha256){throw "source mismatch $($item.module)"}
 & 'D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe' -o "$d/objects/$($item.module).olean" $src *> "$d/$($item.module).log"
 if($LASTEXITCODE -ne 0){throw "compile failed $($item.module)"}
 $after=([BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash([IO.File]::ReadAllBytes($src)))).Replace('-','').ToLower()
 if($after -ne $before){throw "source changed $($item.module)"}
 $log=Get-Content -Raw "$d/$($item.module).log"
 if($log -match 'warning:|error:|sorryAx'){throw "bad output $($item.module)"}
 foreach($report in $item.reports){if(-not $log.Contains("'$report' depends on axioms:")){throw "missing $report"}}
}

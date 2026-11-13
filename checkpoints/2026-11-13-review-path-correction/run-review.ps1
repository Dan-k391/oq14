$ErrorActionPreference='Stop'
$dir=(Resolve-Path '../checkpoints/2026-11-13-review-path-correction').Path
$objs=Join-Path $dir 'objects'
$lake='D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe'
$lean='D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe'
$base=& $lake env powershell -NoProfile -Command '$env:LEAN_PATH'
$env:LEAN_PATH="$objs;$base"
$a=Get-Content -Raw '../checkpoints/2026-11-13-phase-gluing/reviews/independent-build.json'|ConvertFrom-Json
$b=Get-Content -Raw '../checkpoints/2026-11-13-rounded-peak-family/reviews/independent-build.json'|ConvertFrom-Json
$c=Get-Content -Raw '../checkpoints/2026-11-13-compact-phase-representative/reviews/independent-build.json'|ConvertFrom-Json
$order=@($a)+@($b)+@($c);$records=@()
foreach($entry in $order){
 $m=$entry.module;$src=(Resolve-Path "$m.lean").Path;$hash=(Get-FileHash $src).Hash.ToLower();if($hash -ne $entry.source_sha256){throw "source hash mismatch $m"}
 $obj=Join-Path $objs "$m.olean";$log=Join-Path $dir "$m.log";$watch=[Diagnostics.Stopwatch]::StartNew();& $lean -o $obj $src *> $log;$rc=$LASTEXITCODE;$watch.Stop();if($rc -ne 0){throw "build failure $m"}
 $out=Get-Content -Raw $log;if($out -match 'warning:|sorryAx|error:'){throw "bad diagnostics $m"};$count=([regex]::Matches($out,'depends on axioms:')).Count;if($count -ne $entry.reports){throw "report mismatch $m"}
 $decl=@(Select-String -Path $src -Pattern '^#print axioms (.+)$'|ForEach-Object {$_.Matches[0].Groups[1].Value})
 $records += [ordered]@{module=$m;source_path=$src;source_sha256=$hash;object_path=$obj;object_sha256=(Get-FileHash $obj).Hash.ToLower();log_path=$log;log_sha256=(Get-FileHash $log).Hash.ToLower();exit_code=$rc;seconds=$watch.Elapsed.TotalSeconds;declarations=$decl;reports=$count;command="$lean -o $obj $src";cwd=(Get-Location).Path;lean_path=$env:LEAN_PATH;retained_object_verified=$true;status='pass'}
 Write-Output "$m passed"
}
[IO.File]::WriteAllText((Join-Path $dir 'independent-build.json'),(($records|ConvertTo-Json -Depth 5)+"`n"),[Text.UTF8Encoding]::new($false))

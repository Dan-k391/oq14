$ErrorActionPreference='Stop'
function Get-Sha([string]$path) {
  $stream=[System.IO.File]::OpenRead((Resolve-Path $path).Path)
  try { $sha=[System.Security.Cryptography.SHA256]::Create(); return ([System.BitConverter]::ToString($sha.ComputeHash($stream))).Replace('-','').ToLower() }
  finally { $stream.Dispose() }
}
$review='D:/oq14/checkpoints/2026-11-13-curved-scalar-review'
$env:LEAN_PATH="$review/objects;$env:LEAN_PATH"
$lists=@('packet05-curved-author-manifest.json','packet05-scalar-iteration-author-manifest.json')
$records=@()
foreach($file in $lists){
  $m=Get-Content -Raw "D:/oq14/checkpoints/2026-11-12-full-closure/$file" | ConvertFrom-Json
  $entries=if($m.modules){$m.modules}else{$m.records}
  foreach($e in $entries){
    $name=$e.module; $source="$name.lean"; $log="$review/logs/$name.log"; $object="$review/objects/$name.olean"
    $before=(Get-Sha $source)
    if($before -ne $e.source_sha256.ToLower()){throw "Source hash mismatch $name"}
    & D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe -o $object $source *> $log
    $exit=$LASTEXITCODE; $output=Get-Content -Raw $log; $after=(Get-Sha $source)
    $count=([regex]::Matches($output,'depends on axioms:')).Count
    if($exit -ne 0 -or $output -match 'warning:|error:|sorryAx' -or $before -ne $after){throw "Build failed $name"}
    if($e.reports -and $count -ne $e.reports.Count){throw "Report count mismatch $name"}
    if($null -ne $e.report_count -and $count -ne $e.report_count){throw "Report count mismatch $name"}
    $records+= [ordered]@{module=$name;source_sha256=$after;object_sha256=(Get-Sha $object);log_sha256=(Get-Sha $log);reports=$count;status='pass'}
    [System.IO.File]::WriteAllText("$review/build-progress.json",(($records|ConvertTo-Json -Depth 6)+"`n"),[System.Text.UTF8Encoding]::new($false))
    Write-Output "$name : $count reports"
  }
}
[System.IO.File]::Copy("$review/build-progress.json","$review/build-manifest.json",$true)

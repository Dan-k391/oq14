param([string]$Out = 'checkpoints/2026-11-13-driven-components/provenance-audit.json')
$ErrorActionPreference='Stop'
$root=(Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
Set-Location $root
$lean=Join-Path $root 'lean'
$ev=Join-Path $root 'checkpoints/2026-10-27-continuation/evidence'
$stage=@{}; Get-Content 'checkpoints/2026-11-13-modal-transport/evidence/audited_after_5238-stage74.json' -Raw | ConvertFrom-Json | ForEach-Object { $stage[$_.module]=$_.source_sha256.ToLower() }
$release=Get-Content 'checkpoints/2026-10-23-resume/evidence/clean-release-5238/lean/provenance.json' -Raw | ConvertFrom-Json
$clean=@{}; $release.source_hashes.PSObject.Properties | ForEach-Object { if ($_.Name.EndsWith('.lean')) { $clean[$_.Name.Substring(0,$_.Name.Length-5).Replace('/','.').Replace('\','.')]=$_.Value.ToLower() } }
function Hash([byte[]]$b) { [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($b)).ToLower() }
function Norm([byte[]]$b) { $text=[Text.Encoding]::UTF8.GetString($b); return ,([Text.Encoding]::UTF8.GetBytes($text.Replace("`r`n","`n"))) }
$expected=@{}; @($stage.Values)+@($clean.Values) | ForEach-Object { $expected[$_]=1 }
$archive=@{}
Add-Type -AssemblyName System.IO.Compression.FileSystem
Get-ChildItem $ev -Filter 'stage*-raw-evidence.zip' | ForEach-Object {
  $zip=[IO.Compression.ZipFile]::OpenRead($_.FullName)
  try { foreach ($entry in $zip.Entries) { if ($entry.FullName.EndsWith('.lean')) { $stream=$entry.Open(); $mem=[IO.MemoryStream]::new(); $stream.CopyTo($mem); $stream.Dispose(); $b=$mem.ToArray(); $mem.Dispose(); $hash=Hash $b; if ($expected.ContainsKey($hash)) { $archive[$hash]=Hash (Norm $b) } } } } finally { $zip.Dispose() }
}
$roots=@((Get-Content (Join-Path $PSScriptRoot '../modules.json') -Raw | ConvertFrom-Json).module)
$modules=@{}; $external=[Collections.Generic.HashSet[string]]::new(); $missing=[Collections.Generic.List[string]]::new()
function Visit([string]$m) {
 if ($modules.ContainsKey($m)) { return }
 $path=Join-Path $lean ($m.Replace('.','/')+'.lean')
 if (!(Test-Path -LiteralPath $path)) { if ($m -in $roots) { $missing.Add($m) } else { [void]$external.Add($m) }; return }
 $b=[IO.File]::ReadAllBytes($path); $hash=Hash $b; $normalized=Hash (Norm $b); $candidates=@()
 foreach ($entry in @(@('stage74',$stage),@('release5238',$clean))) {
   $label=$entry[0]; $map=$entry[1]
   if ($map.ContainsKey($m)) { $exp=$map[$m]; $match=$null; if ($hash -eq $exp) { $match='raw' } elseif ($archive.ContainsKey($exp) -and $normalized -eq $archive[$exp]) { $match='CRLF_to_LF_archived' } elseif ($normalized -eq $exp) { $match='CRLF_to_LF_expected' }; $candidates+=@{ledger=$label;expected_sha256=$exp;match=$match} }
 }
 $status=if ($m -in $roots) {'new_or_pending'} elseif (@($candidates | Where-Object match).Count) {'matched'} elseif ($candidates.Count) {'hash_mismatch'} else {'unlisted'}
 $imports=@(); foreach ($line in [IO.File]::ReadAllLines($path)) { if ($line -match '^\s*import\s+([^\r\n-]+)') { $imports+=@([regex]::Matches($Matches[1],"[A-Za-z_][\w.']*") | ForEach-Object Value) } }
 $modules[$m]=@{path=[IO.Path]::GetRelativePath($root,$path);sha256=$hash;normalized_sha256=$normalized;status=$status;frozen_candidates=$candidates;imports=$imports}
 foreach ($x in $imports) { Visit $x }
}
foreach ($m in $roots) { Visit $m }
$manifest=Get-Content (Join-Path $lean 'lake-manifest.json') -Raw | ConvertFrom-Json
$mp=$manifest.packages | Where-Object name -eq 'mathlib'
$leanver=& (Join-Path $root '.tools/lean/lean-4.19.0-windows/bin/lean.exe') --version
$head=git -C (Join-Path $lean '.lake/packages/mathlib') rev-parse HEAD
$toolchain=@{lean_toolchain=(Get-Content (Join-Path $lean 'lean-toolchain') -Raw).Trim(); lean_version=$leanver; mathlib_manifest_rev=$mp.rev; mathlib_git_head=$head; mathlib_expected=$release.mathlib_revision}
$counts=@{}; $modules.Values | Group-Object status | ForEach-Object {$counts[$_.Name]=$_.Count}
$result=@{roots=$roots;missing_roots=@($missing);toolchain=$toolchain;counts=$counts;modules=$modules;nonlocal_imports=@($external);method='Raw current source hashes against frozen stage74 and release5238 manifests; CRLF-to-LF equivalence only against archive bytes authenticated by raw frozen hash, or normalized current hash equal to frozen raw hash. Root modules classified new or pending.'}
$result | ConvertTo-Json -Depth 30 | Set-Content -Encoding utf8 $Out
$bad=@{}; foreach ($k in $modules.Keys) { if ($modules[$k].status -in @('unlisted','hash_mismatch')) { $bad[$k]=$modules[$k].status } }
@{counts=$counts;missing_roots=@($missing);unmatched=$bad;toolchain=$toolchain} | ConvertTo-Json -Depth 10

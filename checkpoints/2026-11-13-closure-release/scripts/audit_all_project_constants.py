from pathlib import Path
import os,sys,json,re,hashlib,subprocess,time
r=Path('D:/oq14');l=r/'lean';cp=r/'checkpoints/2026-11-13-aggregate-verification'
stage=sys.argv[1] if len(sys.argv)>1 else '108'
folder=cp/('all-constants-stage'+stage);folder.mkdir(exist_ok=True)
inventory=json.loads((cp/'source-inventory.json').read_text(encoding='utf-8'))
fresh=json.loads((cp/'fresh-build.json').read_text(encoding='utf-8'))
assert fresh['complete'] and fresh['base_commit']==inventory['base_commit']
assert inventory.get('stage')==int(stage), 'Audit stage must match the completed fresh inventory.'
roots=inventory['roots']
fresh_records={x['module']:x for x in fresh['records']}
for rec in fresh_records.values():
 assert hashlib.sha256(Path(rec['object']).read_bytes()).hexdigest()==rec['object_sha256']
 assert hashlib.sha256(Path(rec['log']).read_bytes()).hexdigest()==rec['log_sha256']
modules={}
def visit(m):
 p=l.joinpath(*m.split('.')).with_suffix('.lean')
 if m in modules or not p.exists():return
 b=p.read_bytes();modules[m]=hashlib.sha256(b).hexdigest()
 for line in b.decode('utf-8-sig').splitlines():
  if line.startswith('import '):
   for d in line[7:].split():visit(d)
for m in roots:visit(m)
assert set(modules)==set(fresh_records)
for m,h in modules.items():assert fresh_records[m]['source_sha256']==h
probe=(r/'tmp/AllProjectAxiomAuditProbe.lean').read_text(encoding='utf-8')
code='\n'.join('import '+m for m in roots)+'\nimport Lean.Util.CollectAxioms\n'+probe[probe.index('\nset_option'):]
code=code.replace('Std.HashSet.ofList [`Packet06ModalHotspotExistence]', 'Std.HashSet.ofList ['+', '.join('`'+m for m in modules)+']')
src=folder/'AllProjectAxiomAudit.lean';src.write_text(code,encoding='utf-8',newline='\n')
lake=r/'.tools/lean/lean-4.19.0-windows/bin/lake.exe';env=os.environ.copy()
env.update(json.loads(subprocess.check_output([lake,'env',sys.executable,'-c','import json,os;print(json.dumps(dict(LEAN_PATH=os.environ.get("LEAN_PATH",""))))'],cwd=l,text=True)))
local=(l/'.lake/build/lib/lean').resolve()
paths=[p for p in env['LEAN_PATH'].split(os.pathsep) if (l/p).resolve()!=local]
env['LEAN_PATH']=str(cp/'objects')+os.pathsep+os.pathsep.join(paths)
t=time.monotonic();cmd=[str(lake.with_name('lean.exe')),str(src)]
p=subprocess.run(cmd,cwd=l,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log=folder/'audit.log';log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8');print('\n'.join(txt.splitlines()[-8:]),flush=True)
assert p.returncode==0 and 'error:' not in txt and 'warning:' not in txt
match=re.search(r'AUDIT ALL KERNEL-SAFE PROJECT CONSTANTS: (\d+); UNSAFE IMPLEMENTATIONS EXCLUDED: (\d+); AXIOMS: \[([^]]*)\]',txt)
assert match and set(v.strip() for v in match[3].split(','))<={'propext','Classical.choice','Quot.sound'}
for m,h in modules.items():assert hashlib.sha256(l.joinpath(*m.split('.')).with_suffix('.lean').read_bytes()).hexdigest()==h
result=dict(complete=True,stage=stage,base_commit=inventory['base_commit'],root_count=len(roots),module_count=len(modules),constant_count=int(match[1]),unsafe_implementation_count=int(match[2]),unsafe_implementations=re.findall(r'EXCLUDED UNSAFE IMPLEMENTATION: (.+)',txt),axioms=match[3],source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),fresh_build_sha256=hashlib.sha256((cp/'fresh-build.json').read_bytes()).hexdigest(),inventory_sha256=hashlib.sha256((cp/'source-inventory.json').read_bytes()).hexdigest(),exit_code=0,seconds=round(time.monotonic()-t,3),command=cmd,lean_path=env['LEAN_PATH'],scope='All kernel-safe constants owned by accepted project modules, including private and unprinted declarations, and the union of their complete axiom dependency closures. Unsafe executable implementation declarations are listed separately and cannot be referenced by kernel-safe proofs. Only the three standard axioms are permitted in any safe declaration closure. Uses only source/log/object-hash-authenticated fresh aggregate project objects; cached project build directory is excluded.',modules=modules)
(folder/'result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')

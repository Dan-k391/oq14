from pathlib import Path
import json,re,hashlib,subprocess,sys,shutil
r=Path('D:/oq14');l=r/'lean';cp=r/'checkpoints/2026-11-13-aggregate-verification'
stage=int(sys.argv[1]); ledger_path=Path(sys.argv[2])
if not ledger_path.is_absolute():ledger_path=r/ledger_path
old=json.loads((cp/'fresh-build.json').read_text(encoding='utf-8'))
assert old['complete'], 'Finish the preceding fresh aggregate build before extension.'
old_inventory=json.loads((cp/'source-inventory.json').read_text(encoding='utf-8'))
archive=cp/('completed-'+old['base_commit']);archive.mkdir(exist_ok=True)
for name in ['fresh-build.json','source-inventory.json']:
 dest=archive/name
 if dest.exists():assert dest.read_bytes()==(cp/name).read_bytes()
 else:shutil.copyfile(cp/name,dest)
ledger=json.loads(ledger_path.read_text(encoding='utf-8'))
roots=[x['module'] for x in ledger];mods={};active=set();order=[]
assert len(roots)==len(set(roots)), 'Duplicate accepted roots'
source=lambda m:l.joinpath(*m.split('.')).with_suffix('.lean')
tracked=set(subprocess.check_output(['git','ls-files','--','lean'],cwd=r,text=True).splitlines())
subprocess.run(['git','diff','--exit-code','HEAD','--','lean'],cwd=r,check=True,stdout=subprocess.PIPE)
for rec in ledger:
 assert hashlib.sha256(source(rec['module']).read_bytes()).hexdigest()==rec['source_sha256'], rec['module']+' ledger mismatch'
external=set()
def visit(m):
 if m in mods:return
 p=source(m);assert p.exists() and p.relative_to(r).as_posix() in tracked,m
 assert m not in active,m
 active.add(m);b=p.read_bytes();s=b.decode('utf-8-sig')
 imports=[d for ln in s.splitlines() for hit in [re.match(r'^\s*import\s+(.+)$',ln)] if hit
   for d in hit[1].split('--',1)[0].split()]
 for d in imports:
  if not source(d).exists():
   assert d.split('.')[0] in {'Lean','Mathlib'}, 'Unknown nonlocal import '+d+' in '+m
   external.add(d)
 deps=[d for d in imports if source(d).exists()]
 for d in deps:visit(d)
 active.remove(m)
 mods[m]=dict(module=m,source_sha256=hashlib.sha256(b).hexdigest(),dependencies=deps,
   declarations=re.findall(r'^#print axioms (\S+)',s,re.M))
 order.append(m)
for m in roots:visit(m)
for rec in old['records']:
 assert rec['module'] in mods and rec['source_sha256']==mods[rec['module']]['source_sha256']
head=subprocess.check_output(['git','rev-parse','--short','HEAD'],cwd=r,text=True).strip()
data=dict(base_commit=head,prior_commit=old['base_commit'],stage=stage,
 ledger=ledger_path.relative_to(r).as_posix(),ledger_sha256=hashlib.sha256(ledger_path.read_bytes()).hexdigest(),
 scope=f'All local sources transitively imported by the stage{stage} accepted ledger; prior fresh builds retained only after exact source, log and object hash authentication. No cached project objects.',
 roots=roots,nonlocal_imports=sorted(external),tracked_lean_sources_match_head=True,
 ledger_root_hashes_authenticated=True,modules=[mods[m] for m in order])
(cp/'source-inventory.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Extended inventory:',len(roots),'roots;',len(mods),'modules;',len(mods)-len(old['records']),'new fresh builds')

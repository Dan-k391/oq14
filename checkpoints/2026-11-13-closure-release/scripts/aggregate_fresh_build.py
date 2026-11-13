from pathlib import Path
import json,os,re,hashlib,subprocess,time,concurrent.futures
r=Path('D:/oq14');l=r/'lean';cp=r/'checkpoints/2026-11-13-aggregate-verification'
obj=cp/'objects';logs=cp/'logs';obj.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
inventory=json.loads((cp/'source-inventory.json').read_text(encoding='utf-8'))
ledger_path=r/inventory['ledger']
assert hashlib.sha256(ledger_path.read_bytes()).hexdigest()==inventory['ledger_sha256']
ledger=json.loads(ledger_path.read_text(encoding='utf-8'))
assert [x['module'] for x in ledger]==inventory['roots']
mods={v['module']:v for v in inventory['modules']};done={};pending=set(mods);running={}
assert len(mods)==len(inventory['modules'])
for rec in ledger:assert mods[rec['module']]['source_sha256']==rec['source_sha256']
lake=r/'.tools/lean/lean-4.19.0-windows/bin/lake.exe'
env=os.environ.copy()
probe=json.loads(subprocess.check_output([lake,'env',os.sys.executable,'-c','import json,os;print(json.dumps(dict(LEAN_PATH=os.environ.get("LEAN_PATH",""))))'],cwd=l,text=True))
paths=probe['LEAN_PATH'].split(os.pathsep)
local=(l/'.lake/build/lib/lean').resolve()
paths=[p for p in paths if (l/p).resolve()!=local]
env['LEAN_PATH']=str(obj)+os.pathsep+os.pathsep.join(paths)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=lambda m:l.joinpath(*m.split('.')).with_suffix('.lean')
for m,a in mods.items():
 assert sha(source(m))==a['source_sha256'],m+' inventory source mismatch'
 imports=[d for ln in source(m).read_text(encoding='utf-8-sig').splitlines()
   for hit in [re.match(r'^\s*import\s+(.+)$',ln)] if hit for d in hit[1].split('--',1)[0].split()]
 assert [d for d in imports if source(d).exists()]==a['dependencies'],m+' dependency mismatch'
 for d in imports:
  assert d in mods or (not source(d).exists() and d.split('.')[0] in {'Lean','Mathlib'}),m+' unknown dependency '+d
start=time.monotonic()
prior_elapsed=0
status=cp/'fresh-build.json'
if status.exists():
 old=json.loads(status.read_text(encoding='utf-8'))
 assert old['base_commit'] in {inventory['base_commit'],inventory.get('prior_commit')}
 prior_elapsed=old['elapsed_seconds']
 for record in old['records']:
  m=record['module']
  assert record['source_sha256']==mods[m]['source_sha256']==sha(source(m))
  assert sha(Path(record['object']))==record['object_sha256']
  assert sha(Path(record['log']))==record['log_sha256']
  done[m]=record;pending.remove(m)
def build(m):
 a=mods[m];src=source(m);out=obj.joinpath(*m.split('.')).with_suffix('.olean');log=logs/(m+'.log')
 out.parent.mkdir(parents=True,exist_ok=True)
 assert sha(src)==a['source_sha256'],m+' source changed before build'
 cmd=[str(lake.with_name('lean.exe')),'-o',str(out),str(src)]
 t=time.monotonic();p=subprocess.run(cmd,cwd=l,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log.write_bytes(p.stdout);s=p.stdout.decode('utf-8',errors='replace')
 ax=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",s)
 assert p.returncode==0,(m,s[-6000:])
 assert sha(src)==a['source_sha256'],m+' source changed during build'
 assert len(ax)==len(a['declarations']),(m,'report count mismatch')
 assert all(actual==requested or actual.endswith('.'+requested)
   for (actual,_),requested in zip(ax,a['declarations'])),(m,'report name mismatch')
 for _,xs in ax:assert set(x.strip() for x in xs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},(m,xs)
 assert 'sorryAx' not in s,(m,'sorryAx')
 return dict(module=m,source_sha256=a['source_sha256'],command=cmd,exit_code=0,
   seconds=round(time.monotonic()-t,3),log=str(log),log_sha256=sha(log),object=str(out),object_sha256=sha(out),
   reports=len(ax),declarations=[n for n,_ in ax],requested_declarations=a['declarations'],
   warnings=[ln for ln in s.splitlines() if 'warning:' in ln])
def save(complete,error=None):
 (cp/'fresh-build.json').write_text(json.dumps(dict(complete=complete,error=error,base_commit=inventory['base_commit'],
   scope=inventory.get('scope','All project sources transitively imported by every stage107 ledger module, freshly rebuilt. Mathlib/package objects cached. Project cached build directory excluded from LEAN_PATH.'),
   lean_path=env['LEAN_PATH'],elapsed_seconds=round(prior_elapsed+time.monotonic()-start,2),module_count=len(done),expected_module_count=len(mods),
   records=[done[m] for m in mods if m in done]),indent=2)+'\n',encoding='utf-8',newline='\n')
print('Fresh build resuming:',len(done),'verified;',len(mods),'project modules; 8 compiler workers',flush=True)
try:
 with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
  while pending or running:
   ready=[m for m in mods if m in pending and all(d in done for d in mods[m]['dependencies'])]
   while ready and len(running)<8:
    m=ready.pop(0);pending.remove(m);running[pool.submit(build,m)]=m
   assert running,'dependency cycle or missing dependency'
   finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in finished:
    m=running.pop(f);done[m]=f.result()
   if len(done)%10==0 or len(done)==len(mods):
    save(False);print('Passed',len(done),'/',len(mods),'elapsed',round(time.monotonic()-start),'seconds',flush=True)
 save(True);print('COMPLETE',len(done),'modules',sum(x['reports'] for x in done.values()),'reports',flush=True)
except BaseException as e:
 save(False,repr(e));print('FAILED',repr(e),flush=True);raise

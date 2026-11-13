import concurrent.futures, hashlib, json, os, pathlib, subprocess, sys
base=pathlib.Path('D:/oq14'); lean=base/'lean'; review=base/'checkpoints/2026-11-13-curved-scalar-review'
files=['packet05-curved-author-manifest.json','packet05-scalar-iteration-author-manifest.json']
entries=[]
for file in files:
    m=json.loads((base/'checkpoints/2026-11-12-full-closure'/file).read_text(encoding='utf-8-sig'))
    entries.extend(m['modules'])
byname={e['module']:e for e in entries}; assert len(byname)==len(entries)
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
progress=review/'build-progress.json'
records=json.loads(progress.read_text(encoding='utf-8-sig')) if progress.exists() else []
if isinstance(records,dict): records=[records]
done={r['module']:r for r in records}
for name,r in done.items():
    if name not in byname or sha(lean/(name+'.lean'))!=r['source_sha256'] or sha(review/'objects'/(name+'.olean'))!=r['object_sha256']:
        raise RuntimeError('stale preexisting record: '+name)
env=os.environ.copy(); env['LEAN_PATH']=str(review/'objects')+';'+env['LEAN_PATH']
exe='D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lean.exe'
def build(e):
    name=e['module']; src=lean/(name+'.lean'); obj=review/'objects'/(name+'.olean'); log=review/'logs'/(name+'.log')
    before=sha(src)
    if before!=e['source_sha256'].lower(): raise RuntimeError('source hash mismatch '+name)
    r=subprocess.run([exe,'-o',str(obj),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_bytes(r.stdout); output=r.stdout.decode('utf-8',errors='replace'); after=sha(src)
    import re
    ax=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output,flags=re.S)
    expected={'propext','Classical.choice','Quot.sound'}
    if r.returncode or 'warning:' in output or 'error:' in output or 'sorryAx' in output or before!=after: raise RuntimeError('compile failed '+name+'\n'+output)
    if len(ax)!=len(e['reports']) or any(set(x.strip() for x in a.split(','))!=expected for a in ax): raise RuntimeError('axiom inventory mismatch '+name+'\n'+output)
    return {'module':name,'source_sha256':after,'object_sha256':sha(obj),'log_sha256':sha(log),'reports':len(ax),'status':'pass'}
def save(): progress.write_text(json.dumps([done[e['module']] for e in entries if e['module'] in done],indent=2)+'\n',encoding='utf-8')
running={}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    while len(done)<len(entries):
        for e in entries:
            name=e['module']
            if len(running)>=2: break
            if name in done or name in running.values(): continue
            deps=[i for i in e['imports'] if i in byname]
            if all(i in done for i in deps): running[pool.submit(build,e)]=name
        if not running: raise RuntimeError('unresolved build dependency')
        completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for fut in completed:
            name=running.pop(fut); done[name]=fut.result(); save(); print(name,':',done[name]['reports'],'reports',flush=True)
(review/'build-manifest.json').write_text(progress.read_text(encoding='utf-8'),encoding='utf-8')

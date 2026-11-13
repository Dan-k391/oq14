import os,json,hashlib,pathlib,subprocess,time
root=pathlib.Path(r'D:\oq14');lean=root/'lean';dst=root/'checkpoints/2026-11-13-weighted-rounding';mods=['Packet06WeightedStaticLimit','Packet06WeightedRemainderLimit','Packet06WeightedPencilLimit','Packet06WeightedPencilHolomorphic'];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();records=[]
for name in mods:
 src=lean/(name+'.lean');obj=lean/'.lake/build/lib/lean'/(name+'.olean');log=dst/(name+'.log');t=time.time();p=subprocess.run([r'D:\oq14\.tools\lean\lean-4.19.0-windows\bin\lean.exe','-o',str(obj),str(src)],cwd=lean,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8',errors='replace');r=dict(module=name,source_sha256=h(src),log_sha256=h(log),object_sha256=h(obj) if obj.exists() else None,exit_code=p.returncode,reports=txt.count('depends on axioms:'),warnings='warning:' in txt,bad_axioms='sorryAx' in txt or 'error:' in txt,seconds=round(time.time()-t,2));records.append(r);print(r,flush=True)
 (dst/'author-build.json').write_text(json.dumps(dict(complete=False,records=records),indent=2)+'\n',encoding='utf-8')
 if p.returncode or r['warnings'] or r['bad_axioms']: break
else:(dst/'author-build.json').write_text(json.dumps(dict(complete=True,scope='Author ordered build; cached upstream, no claim of independent review.',records=records),indent=2)+'\n',encoding='utf-8')

import os,json,hashlib,subprocess,time,pathlib
root=pathlib.Path(r'D:\oq14'); lean=root/'lean'; rev=root/'checkpoints/2026-11-13-physical-green/reviews';obj=rev/'fresh-objects';obj.mkdir(exist_ok=True)
mods=['Packet06BallObservation','Packet06GreenSource','Packet06GreenPhysical','Packet06GreenResidue','Packet06GreenSector'];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();env=os.environ.copy();env['LEAN_PATH']=str(obj)+os.pathsep+env.get('LEAN_PATH','');records=[]
for name in mods:
 src=lean/(name+'.lean');out=obj/(name+'.olean');log=rev/(name+'.log'); t=time.time();p=subprocess.run([r'D:\oq14\.tools\lean\lean-4.19.0-windows\bin\lean.exe','-o',str(out),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8',errors='replace');r=dict(module=name,source_sha256=h(src),log_sha256=h(log),object_sha256=h(out) if out.exists() else None,exit_code=p.returncode,reports=txt.count('depends on axioms:'),warnings='warning:' in txt,bad_axioms='sorryAx' in txt or 'error:' in txt,seconds=round(time.time()-t,2));records.append(r); print(r,flush=True)
 (rev/'independent-build.json').write_text(json.dumps(dict(complete=False,records=records),indent=2)+'\n',encoding='utf-8')
 if p.returncode or r['warnings'] or r['bad_axioms']: break
else:(rev/'independent-build.json').write_text(json.dumps(dict(complete=True,scope='Independent ordered five-module build using fresh objects and cached upstream dependencies.',records=records),indent=2)+'\n',encoding='utf-8')

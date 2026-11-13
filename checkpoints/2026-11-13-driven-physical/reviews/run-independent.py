import os,json,hashlib,subprocess,time,pathlib
root=pathlib.Path(r'D:\oq14');lean=root/'lean';rev=root/'checkpoints/2026-11-13-driven-physical/reviews';obj=rev/'fresh-objects';obj.mkdir(exist_ok=True);m=json.loads((root/'checkpoints/2026-11-12-full-closure/packet07-physical-inventory.json').read_text(encoding='utf-8'))
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();env=os.environ.copy();env['LEAN_PATH']=str(obj)+os.pathsep+env.get('LEAN_PATH','');records=[]
for rec in m['modules']:
 name=rec['module'];src=root/rec['source'];out=obj/(name+'.olean');log=rev/(name+'.log');actual=h(src)
 if actual!=rec['source_sha256']: print('MISMATCH',name,actual,flush=True);break
 t=time.time();p=subprocess.run([r'D:\oq14\.tools\lean\lean-4.19.0-windows\bin\lean.exe','-o',str(out),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8',errors='replace');r=dict(module=name,source_sha256=actual,log_sha256=h(log),object_sha256=h(out) if out.exists() else None,exit_code=p.returncode,reports=txt.count('depends on axioms:'),expected_reports=len(rec['reports']),warnings='warning:' in txt,bad_axioms='sorryAx' in txt or 'error:' in txt,seconds=round(time.time()-t,2));records.append(r);print(r,flush=True)
 (rev/'independent-build.json').write_text(json.dumps(dict(complete=False,records=records),indent=2)+'\n',encoding='utf-8')
 if p.returncode or r['warnings'] or r['bad_axioms'] or r['reports']!=r['expected_reports']:break
else:(rev/'independent-build.json').write_text(json.dumps(dict(complete=True,scope='Independent ordered five-module build using fresh objects and cached upstream dependencies.',records=records),indent=2)+'\n',encoding='utf-8')

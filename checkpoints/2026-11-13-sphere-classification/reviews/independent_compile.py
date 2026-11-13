from pathlib import Path
import json, subprocess, os, sys, hashlib, re, time
root=Path(r'D:\oq14'); lean=root/'lean'; prior=root/'checkpoints/2026-11-13-sphere-recovery'; out=root/'checkpoints/2026-11-13-sphere-classification/reviews'; obj=out/'independent-objects'; obj.mkdir(exist_ok=True)
lake=root/'.tools/lean/lean-4.19.0-windows/bin/lake.exe'; compiler=lake.with_name('lean.exe')
probe=subprocess.check_output([str(lake),'env',sys.executable,'-c','import os,json; print(json.dumps({k:os.environ.get(k, "") for k in ["LEAN_PATH","LEAN_SRC_PATH"]}))'],cwd=lean,text=True)
env=os.environ.copy(); env.update(json.loads(probe)); env['LEAN_PATH']=str(obj)+os.pathsep+env['LEAN_PATH']
mods=json.loads((prior/'modules.json').read_text(encoding='utf-8')); records=[]; allowed={'propext','Classical.choice','Quot.sound'}
for m in mods:
 name=m['module']; src=lean/(name+'.lean'); snap=prior/'sources'/(name+'.lean'); data=src.read_bytes(); assert data==snap.read_bytes(),name
 t=time.monotonic(); proc=subprocess.run([str(compiler),'-o',str(obj/(name+'.olean')),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=out/(name+'-independent.log'); log.write_bytes(proc.stdout); output=proc.stdout.decode('utf-8','replace'); reps=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",output)
 rec={'module':name,'source_sha256':hashlib.sha256(data).hexdigest(),'log_sha256':hashlib.sha256(proc.stdout).hexdigest(),'exit_code':proc.returncode,'elapsed_s':round(time.monotonic()-t,2),'reports':len(reps)}; records.append(rec)
 (out/'independent-build.json').write_text(json.dumps({'complete':False,'records':records},indent=2)+'\n',encoding='utf-8')
 assert proc.returncode==0 and 'warning:' not in output, (name,output)
 assert [n for n,_ in reps]==m['declarations'],name
 assert all({s.strip() for s in a.split(',') if s.strip()} <= allowed for _,a in reps),name
 print(name, 'PASS',len(reps),flush=True)
(out/'independent-build.json').write_text(json.dumps({'complete':True,'scope':'14 fresh independent module objects, cached upstream dependencies; not a full clean rebuild','records':records},indent=2)+'\n',encoding='utf-8')

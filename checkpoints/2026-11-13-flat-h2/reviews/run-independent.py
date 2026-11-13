import os,json,hashlib,subprocess,time,pathlib
root=pathlib.Path(r'D:\oq14'); lean=root/'lean'; review=root/'checkpoints/2026-11-13-flat-h2/reviews'; obj=review/'fresh-objects'; obj.mkdir(exist_ok=True)
m=json.loads((root/'checkpoints/2026-11-12-full-closure/packet05-frozen-author-manifest.json').read_text(encoding='utf-8'))
hashf=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
env=os.environ.copy(); env['LEAN_PATH']=str(obj)+os.pathsep+env.get('LEAN_PATH','')
records=[]
for rec in m['records']:
 name=rec['module']; src=lean/(name+'.lean'); log=review/(name+'.log'); out=obj/(name+'.olean'); actual=hashf(src)
 if actual != rec['source_sha256']:
  print('SOURCE MISMATCH',name,flush=True); break
 t=time.time(); proc=subprocess.run([r'D:\\oq14\\.tools\\lean\\lean-4.19.0-windows\\bin\\lean.exe','-o',str(out),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); log.write_bytes(proc.stdout)
 text=proc.stdout.decode('utf-8',errors='replace'); record=dict(module=name,source_sha256=actual,log_sha256=hashf(log),object_sha256=hashf(out) if out.exists() else None,exit_code=proc.returncode,reports=text.count('depends on axioms:'),elapsed_s=round(time.time()-t,2),warnings='warning:' in text,bad_axioms=('sorryAx' in text or 'error:' in text))
 records.append(record); print(name,proc.returncode,record['reports'],flush=True)
 (review/'independent-build.json').write_text(json.dumps(dict(complete=False,records=records),indent=2)+'\n',encoding='utf-8')
 if proc.returncode or record['warnings'] or record['bad_axioms']: break
else:
 audit=review/'Packet05IndependentAudit.lean'; audit.write_text('\n'.join('import '+x['module'] for x in m['records'])+'\n\n'+'\n'.join('#print axioms '+th for x in m['records'] for th in x['theorems'])+'\n',encoding='utf-8',newline='\n')
 proc=subprocess.run([r'D:\\oq14\\.tools\\lean\\lean-4.19.0-windows\\bin\\lean.exe',str(audit)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); log=review/'Packet05IndependentAudit.log'; log.write_bytes(proc.stdout); text=proc.stdout.decode('utf-8',errors='replace'); a=dict(source_sha256=hashf(audit),log_sha256=hashf(log),exit_code=proc.returncode,reports=text.count('depends on axioms:'),warnings='warning:' in text,bad_axioms=('sorryAx' in text or 'error:' in text)); print('AUDIT',a,flush=True)
 result=dict(complete=proc.returncode==0 and not a['warnings'] and not a['bad_axioms'],scope='Fresh 34-module ordered build with isolated objects and cached upstream dependencies; explicit public declaration axiom audit.',records=records,audit=a)
 (review/'independent-build.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')

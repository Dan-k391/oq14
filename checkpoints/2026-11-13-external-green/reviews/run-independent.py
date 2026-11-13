import os,json,hashlib,subprocess,time,pathlib,tempfile
root=pathlib.Path(r'D:\oq14');lean=root/'lean';rev=root/'checkpoints/2026-11-13-external-green/reviews';rev.mkdir(parents=True,exist_ok=True)
author=json.loads((root/'checkpoints/2026-11-13-external-green/author-manifest.json').read_text(encoding='utf-8'));records=[];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='oq14-external-review-') as tmp:
 env=os.environ.copy();env['LEAN_PATH']=tmp+os.pathsep+env.get('LEAN_PATH','')
 for item in author:
  name=item['module'];src=lean/(name+'.lean');out=pathlib.Path(tmp)/(name+'.olean');log=rev/(name+'.log');start=time.monotonic()
  if sha(src)!=item['source_sha256']: print('HASH MISMATCH',name,flush=True);break
  p=subprocess.run([str(root/'.tools/lean/lean-4.19.0-windows/bin/lean.exe'),'-o',str(out),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8',errors='replace')
  rec={'module':name,'source_sha256':sha(src),'author_hash_match':True,'log_sha256':sha(log),'object_sha256':sha(out) if out.exists() else None,'exit_code':p.returncode,'reports':txt.count('depends on axioms:'),'expected_reports':item['reports'],'warnings':'warning:' in txt,'bad_axioms':'sorryAx' in txt or 'error:' in txt,'seconds':round(time.monotonic()-start,2)};records.append(rec);print(name,p.returncode,rec['reports'],flush=True)
  (rev/'independent-build.json').write_text(json.dumps({'complete':False,'records':records},indent=2)+'\n',encoding='utf-8')
  if p.returncode or rec['warnings'] or rec['bad_axioms'] or rec['reports']!=item['reports']:break
 else:(rev/'independent-build.json').write_text(json.dumps({'complete':True,'scope':'Fresh isolated ordered module objects ahead of cached upstream imports; all source hashes compared to frozen author manifest.','records':records},indent=2)+'\n',encoding='utf-8')

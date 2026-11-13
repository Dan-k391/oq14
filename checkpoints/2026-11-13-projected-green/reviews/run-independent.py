import os,json,hashlib,subprocess,time,pathlib,tempfile,re
root=pathlib.Path(r'D:\oq14');lean=root/'lean';rev=root/'checkpoints/2026-11-13-projected-green/reviews';rev.mkdir(parents=True,exist_ok=True)
author=[]
for name in ['external-green','projected-green']: author+=json.loads((root/('checkpoints/2026-11-13-'+name+'/author-manifest.json')).read_text(encoding='utf-8'))
records=[];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='oq14-projected-review-') as tmp:
 env=os.environ.copy();env['LEAN_PATH']=tmp+os.pathsep+env.get('LEAN_PATH','')
 for item in author:
  name=item['module'];src=lean/(name+'.lean');out=pathlib.Path(tmp)/(name+'.olean');log=rev/(name+'.log');start=time.monotonic()
  if sha(src)!=item['source_sha256']: print('HASH MISMATCH',name,flush=True);break
  p=subprocess.run([str(root/'.tools/lean/lean-4.19.0-windows/bin/lean.exe'),'-o',str(out),str(src)],cwd=lean,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(p.stdout);txt=p.stdout.decode('utf-8',errors='replace')
  blocks=re.findall(r'depends on axioms: \[(.*?)\]',txt,re.S);bad=any(set(re.findall(r'[\w.]+',b))-{'propext','Classical.choice','Quot.sound'} for b in blocks)
  rec={'module':name,'source_sha256':sha(src),'author_hash_match':True,'log_sha256':sha(log),'object_sha256':sha(out) if out.exists() else None,'exit_code':p.returncode,'reports':len(blocks),'expected_reports':item['reports'],'warnings':'warning:' in txt,'bad_axioms':bad or 'sorryAx' in txt or 'error:' in txt,'seconds':round(time.monotonic()-start,2)};records.append(rec);print(name,p.returncode,len(blocks),flush=True)
  (rev/'independent-build.json').write_text(json.dumps({'complete':False,'records':records},indent=2)+'\n',encoding='utf-8')
  if p.returncode or rec['warnings'] or rec['bad_axioms'] or len(blocks)!=item['reports']:break
 else:(rev/'independent-build.json').write_text(json.dumps({'complete':True,'scope':'Fresh isolated ordered objects for both refreshed batches ahead of cached upstream imports; source hashes match both author manifests.','records':records},indent=2)+'\n',encoding='utf-8')

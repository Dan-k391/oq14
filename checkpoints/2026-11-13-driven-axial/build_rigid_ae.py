import pathlib,subprocess,hashlib,json
r=pathlib.Path(r'D:\oq14'); q=r/'checkpoints/2026-11-13-driven-axial'; rows=[]
for m in ['Packet07DrivenFrameAE','Packet07DrivenRigidAE']:
 p=r/'lean'/(m+'.lean');p.write_bytes(p.read_bytes().replace(b'\r\n',b'\n').rstrip(b'\n')+b'\n');o=r/'lean/.lake/build/lib/lean'/(m+'.olean');l=q/(m+'.log');a=subprocess.run([str(r/'.tools/lean/lean-4.19.0-windows/bin/lake.exe'),'env','lean','-o',str(o),str(p)],cwd=r/'lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT);l.write_bytes(a.stdout);h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();t=a.stdout.decode();rows.append({'module':m,'source':str(p),'source_sha256':h(p),'log':str(l),'log_sha256':h(l),'object':str(o),'object_sha256':h(o),'exit_code':a.returncode,'reports':t.count('depends on axioms:')});print(m,a.returncode,flush=True);assert not a.returncode and 'warning:' not in t and 'sorryAx' not in t
(q/'rigid-ae-author-build.json').write_text(json.dumps({'modules':rows},indent=2)+'\n')

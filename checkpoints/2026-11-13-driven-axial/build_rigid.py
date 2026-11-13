import pathlib,subprocess,hashlib,json,os
root=pathlib.Path(r'D:\oq14'); lean=root/'lean'; out=root/'checkpoints/2026-11-13-driven-axial'; out.mkdir(exist_ok=True)
mods=['Packet07DrivenUniformFixedTargetStrong','Packet07DrivenFrameAffine','Packet07DrivenAffineLocal','Packet07DrivenAffineGood','Packet07DrivenAngularTranslationSmooth','Packet07DrivenRigidHotspot','Packet07DrivenRigidFields','Packet07DrivenRigidAngular','Packet07DrivenRigidGeometry']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for m in mods:
 p=lean/(m+'.lean'); p.write_bytes(p.read_bytes().replace(b'\r\n',b'\n').rstrip(b'\n')+b'\n')
 log=out/(m+'.log'); obj=lean/'.lake/build/lib/lean'/(m+'.olean')
 proc=subprocess.run([str(root/'.tools/lean/lean-4.19.0-windows/bin/lake.exe'),'env','lean','-o',str(obj),str(p)],cwd=lean,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log.write_bytes(proc.stdout); t=proc.stdout.decode('utf-8',errors='replace'); rows.append(dict(module=m,source=str(p),source_sha256=sha(p),log=str(log),log_sha256=sha(log),object=str(obj),object_sha256=sha(obj) if obj.exists() else None,exit_code=proc.returncode,reports=t.count('depends on axioms:')))
 print(m,proc.returncode,flush=True)
 if proc.returncode or 'warning:' in t or 'sorryAx' in t: raise SystemExit('failed '+m)
(out/'rigid-extension-author-build.json').write_text(json.dumps({'modules':rows},indent=2)+'\n')

from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8',errors='replace')
r=Path('D:/oq14');l=r/'lean';cp=r/'checkpoints/2026-11-13-aggregate-verification'
out=cp/'audit-scope';out.mkdir(exist_ok=True)
src=out/'AuditConstantKind.lean';src.write_bytes((r/'tmp/AuditConstantKind.lean').read_bytes())
lake=r/'.tools/lean/lean-4.19.0-windows/bin/lake.exe'
env=os.environ.copy()
env.update(json.loads(subprocess.check_output([lake,'env',sys.executable,'-c','import os,json;print(json.dumps(dict(LEAN_PATH=os.environ.get("LEAN_PATH",""))))'],cwd=l,text=True)))
local=(l/'.lake/build/lib/lean').resolve()
paths=[p for p in env['LEAN_PATH'].split(os.pathsep) if (l/p).resolve()!=local]
env['LEAN_PATH']=str(cp/'objects')+os.pathsep+os.pathsep.join(paths)
cmd=[str(lake.with_name('lean.exe')),str(src)]
p=subprocess.run(cmd,cwd=l,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log=out/'AuditConstantKind.log';log.write_bytes(p.stdout)
text=p.stdout.decode('utf-8');print(text)
assert p.returncode==0 and 'error:' not in text and 'warning:' not in text
assert 'unsafe: true' in text and 'unsafe: false' in text
assert "'Equiv.symm' does not depend on any axioms" in text
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
refs=['Lean/Compiler/Old.lean','Lean/Declaration.lean','Lean/Util/CollectAxioms.lean']
rec=dict(command=cmd,exit_code=0,source_sha256=sha(src),log_sha256=sha(log),lean_path=env['LEAN_PATH'],
 compiler_sources={f:sha(r/'.tools/lean/lean-4.19.0-windows/src/lean'/f) for f in refs})
(out/'probe.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8',newline='\n')

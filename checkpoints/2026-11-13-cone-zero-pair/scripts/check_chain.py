"""Build the uniform cone correction and zero-pair chain into isolated fresh objects.

Frozen upstream project and pinned external dependency objects are cached.
This is not a clean whole-project build. Run with the pinned local toolchain.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
checkpoint = Path(__file__).resolve().parent.parent
root = checkpoint.parent.parent
lean_dir = root / 'lean'
lake = root / '.tools/lean/lean-4.19.0-windows/bin/lake.exe'
compiler = lake.with_name('lean.exe')
evidence = checkpoint / 'evidence'
evidence.mkdir(exist_ok=True)
resume = json.loads((evidence/'chain-build.json').read_text(encoding='utf-8')) if '--resume' in sys.argv else None
run_id = resume['run_id'] if resume else time.strftime('%Y%m%d-%H%M%S') + '-' + str(os.getpid())
objects = root/resume['object_directory'] if resume else checkpoint/'objects'/run_id
if not resume:
    objects.mkdir(parents=True, exist_ok=False)
previous = {r['module']:r for r in resume['records']} if resume else {}
modules = json.loads((checkpoint/'modules.json').read_text(encoding='utf-8'))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def without_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1; i+=2
        elif depth and s.startswith('-/',i): depth-=1; i+=2
        elif depth:
            if s[i]=='\n': out.append('\n')
            i+=1
        elif s.startswith('--',i):
            end=s.find('\n',i); i=len(s) if end<0 else end
        else: out.append(s[i]); i+=1
    assert depth==0
    return ''.join(out)
sha = lambda data: hashlib.sha256(data).hexdigest()
relative = lambda p: p.relative_to(root).as_posix()
version = subprocess.check_output([compiler, '--version'], text=True).strip()
assert 'version 4.19.0,' in version
pin = subprocess.check_output(['git', '-C', str(lean_dir/'.lake/packages/mathlib'),
                              'rev-parse', 'HEAD'], text=True).strip()
assert pin == 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
if resume:
    assert resume['compiler']==version and resume['mathlib_revision']==pin
probe = subprocess.check_output([lake,'env',sys.executable,'-c',
    'import os,json; print(json.dumps({k:os.environ.get(k, "") for k in ["LEAN_PATH","LEAN_SRC_PATH"]}))'],
    cwd=lean_dir,text=True)
env = os.environ.copy()
env.update(json.loads(probe))
env['LEAN_PATH'] = str(objects)+os.pathsep+env['LEAN_PATH']
records = []
finished = set()
all_names = {m['module'] for m in modules}
manifest = dict(compiler=version,mathlib_revision=pin,run_id=run_id,
    object_directory=relative(objects),lean_path=env['LEAN_PATH'],
    scope='Fresh isolated objects for all 12 uniform cone and zero-pair modules; cached frozen upstream dependencies. Not a full-project clean build.',
    complete=False,records=records)
for item in modules:
    module = item['module']
    source = lean_dir/(module+'.lean')
    before = source.read_bytes()
    data = before.decode('utf-8')
    assert '\r' not in data and data.endswith('\n') and not data.endswith('\n\n'), module
    imports = [m for line in data.splitlines() if line.startswith('import ') for m in line[7:].split()]
    assert (set(imports)&all_names) <= finished, module
    assert not re.search(r'\b(sorry|admit)\b|^\s*(axiom|constant)\s',without_comments(data),re.M),module
    namespace = re.findall(r'^namespace (\S+)',data,re.M)
    assert len(namespace)==1,module
    declarations = [namespace[0]+'.'+d for d in re.findall(r'^\s*(?:theorem|lemma)\s+(\S+)',data,re.M)]
    assert set(declarations) <= set(item['declarations']),module
    assert len(set(item['declarations'])) == len(item['declarations']),module
    obj = objects/(module+'.olean')
    command = [str(compiler),'-o',str(obj),str(source)]
    log = evidence/(module+'-chain.log')
    if module in previous:
        prior = previous[module]
        assert prior['source_sha256']==sha(before) and prior['exit_code']==0
        assert prior['log_sha256']==sha(log.read_bytes()) and obj.is_file()
        if 'object_sha256' in prior:
            assert prior['object_sha256']==sha(obj.read_bytes())
        raw_output = log.read_bytes()
        exit_code,elapsed = prior['exit_code'],prior['elapsed_seconds']
    else:
        started = time.monotonic()
        proc = subprocess.run(command,cwd=lean_dir,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        raw_output = proc.stdout
        exit_code,elapsed = proc.returncode,round(time.monotonic()-started,3)
        log.write_bytes(raw_output)
    output = raw_output.decode('utf-8',errors='replace')
    assert source.read_bytes()==before,f'Source changed during build: {module}'
    reports = re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",output)
    rec = dict(module=module,source=relative(source),source_sha256=sha(before),
        command=command,exit_code=exit_code,elapsed_seconds=elapsed,
        log=relative(log),log_sha256=sha(raw_output),
        reports=[dict(declaration=n,axioms=[a.strip() for a in ax.split(',') if a.strip()]) for n,ax in reports])
    records.append(rec)
    (evidence/'chain-build.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
    assert exit_code==0,output
    assert 'warning:' not in output,output
    canonical=lambda n:re.sub(r'^_private\.[^.]+\.\d+\.','',n)
    assert [canonical(n) for n,_ in reports]==item['declarations'],(module,output)
    for name,ax in reports:
        assert {a.strip() for a in ax.split(',') if a.strip()}<=allowed,(name,ax)
    assert obj.is_file()
    rec['object_sha256']=sha(obj.read_bytes())
    finished.add(module)
    label = 'REVALIDATED' if module in previous else 'PASS'
    print(f'{module}: {label} ({len(reports)} standard-only reports)',flush=True)
manifest.update(complete=True,module_count=len(records),report_count=sum(len(r['reports']) for r in records))
(evidence/'chain-build.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(f'COMPLETE: {manifest["module_count"]} modules / {manifest["report_count"]} standard-only reports.')

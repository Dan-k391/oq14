"""Recompile every new Packet 01 module in order, using isolated fresh objects.

The 302 frozen upstream project modules and pinned external libraries are
cached dependencies. This is not a clean rebuild of the whole OQ14 project.
Run from any directory with Python 3.12 and the checked-out pinned toolchain.
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
run_id = time.strftime('%Y%m%d-%H%M%S') + '-' + str(os.getpid())
objects = checkpoint / 'objects' / run_id
objects.mkdir(parents=True, exist_ok=False)
modules = [
    ('KernelRadialMomentBridge', 2),
    ('Packet01MomentIntegrability', 5),
    ('MonopoleFlux', 2),
    ('Packet01WeakDerivative', 4),
    ('Packet01RadialTestReduction', 3),
    ('Packet01Monopole', 2),
    ('Packet01PoloidalCoefficients', 3),
    ('Packet01CoefficientChain', 1),
]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
sha = lambda data: hashlib.sha256(data).hexdigest()
relative = lambda p: p.relative_to(root).as_posix()
version = subprocess.check_output([compiler, '--version'], text=True).strip()
assert 'version 4.19.0,' in version
pin = subprocess.check_output(['git', '-C', str(lean_dir / '.lake/packages/mathlib'),
                              'rev-parse', 'HEAD'], text=True).strip()
assert pin == 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
probe = subprocess.check_output([lake, 'env', sys.executable, '-c',
    'import os,json; print(json.dumps({k:os.environ.get(k, "") for k in ["LEAN_PATH","LEAN_SRC_PATH"]}))'],
    cwd=lean_dir, text=True)
env = os.environ.copy()
env.update(json.loads(probe))
env['LEAN_PATH'] = str(objects) + os.pathsep + env['LEAN_PATH']
records = []
finished = set()
all_names = {name for name, _ in modules}
for module, expected_reports in modules:
    source = lean_dir / (module + '.lean')
    before = source.read_bytes()
    # Reject out-of-order use of any other module in this new proof chain.
    imports = [m for line in before.decode('utf-8').splitlines()
               if line.startswith('import ') for m in line[7:].split()]
    assert (set(imports) & all_names) <= finished, module
    assert not re.search(r'\b(sorry|admit)\b|^\s*(axiom|constant)\s',
                         before.decode('utf-8'), re.M), module
    obj = objects / (module + '.olean')
    command = [str(compiler), '-o', str(obj), str(source)]
    started = time.monotonic()
    proc = subprocess.run(command, cwd=lean_dir, env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = evidence / (module + '-chain.log')
    log.write_bytes(proc.stdout)
    output = proc.stdout.decode('utf-8', errors='replace')
    assert source.read_bytes() == before, f'Source changed while compiling {module}'
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    rec = dict(module=module, source=relative(source), source_sha256=sha(before),
               command=command, exit_code=proc.returncode,
               elapsed_seconds=round(time.monotonic()-started, 3),
               log=relative(log), log_sha256=sha(proc.stdout),
               reports=[dict(declaration=name, axioms=[a.strip() for a in ax.split(',') if a.strip()])
                        for name, ax in reports])
    records.append(rec)
    (evidence / 'chain-build.json').write_text(json.dumps(dict(
        compiler=version, mathlib_revision=pin, run_id=run_id,
        object_directory=relative(objects), lean_path=env['LEAN_PATH'],
        scope='Fresh isolated objects for all new chain modules; cached frozen upstream dependencies.',
        complete=False, records=records), indent=2)+'\n', encoding='utf-8', newline='\n')
    assert proc.returncode == 0, output
    assert 'warning:' not in output, output
    assert len(reports) == expected_reports, (module, output)
    for name, ax in reports:
        assert {a.strip() for a in ax.split(',') if a.strip()} <= allowed, (name, ax)
    assert obj.is_file()
    rec['object_sha256'] = sha(obj.read_bytes())
    finished.add(module)
    print(f'{module}: PASS ({len(reports)} standard-only axiom reports)', flush=True)

manifest = dict(compiler=version, mathlib_revision=pin, run_id=run_id,
    object_directory=relative(objects), lean_path=env['LEAN_PATH'],
    scope='Fresh isolated objects for all eight new chain modules; cached frozen upstream dependencies. Not a full-project clean build.',
    complete=True, module_count=len(records), report_count=sum(len(r['reports']) for r in records),
    records=records)
(evidence / 'chain-build.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(f'COMPLETE: {len(records)} modules; {manifest["report_count"]} standard-only axiom reports.')

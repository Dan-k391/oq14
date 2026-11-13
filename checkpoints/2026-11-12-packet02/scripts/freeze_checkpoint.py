"""Validate final Packet 02 evidence and append the immutable stage-67 ledger."""
from pathlib import Path
import hashlib
import json
import re
import zipfile

checkpoint = Path(__file__).resolve().parent.parent
root = checkpoint.parent.parent
evidence = checkpoint/'evidence'
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
rel = lambda p: p.relative_to(root).as_posix()
write = lambda p,v: p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
chain = load(evidence/'chain-build.json')
assert chain['complete'] and chain['module_count']==24 and chain['report_count']==102
prov = load(checkpoint/'provenance-audit.json')
assert prov['counts']=={'matched':485,'new_or_pending':24} and not prov['missing_roots']
prior_path = root/'checkpoints/2026-11-02-packet01/evidence/audited_after_5238-stage66.json'
prior = load(prior_path)
assert len(prior)==503 and sum(r['reports'] for r in prior)==3654
review_groups = {
    'rotation-independent.txt': '''ComplexSphereMaxwell ComplexMagneticHelmholtz
        ComplexMagneticDivergence ComplexMagneticDebye ComplexMagneticReflection
        Packet02SourceSymmetry Packet02MagneticRotation Packet02GoodRotation Packet02VanishingAlgebra'''.split(),
    'vanishing-independent.txt': '''Packet02GoodSet Packet02MagneticVanishing Packet02DebyeVanishing
        Packet02ExteriorGood Packet02Axis'''.split(),
    'surface-independent.txt': '''Packet02Surface Packet02Majorant Packet02SurfaceGeometry
        Packet02RadialLog Packet02SurfaceL2'''.split(),
    'endpoint-independent.txt': ['Packet02GoodMeasurable','Packet02SphereVanishing','Packet02Chain'],
    'root-independent.txt': ['Packet02LogSquare','Packet02ExteriorSmooth'],
}
reviews = {m:r for r,modules in review_groups.items() for m in modules}
assert len(reviews)==24
old_names = {r['module'] for r in prior}
records = []
declarations = set()
for rec in chain['records']:
    module = rec['module']
    assert module not in old_names
    source,log = root/rec['source'],root/rec['log']
    review = checkpoint/'reviews'/reviews[module]
    assert sha(source.read_bytes())==rec['source_sha256']
    assert sha(log.read_bytes())==rec['log_sha256']
    assert prov['modules'][module]['sha256']==rec['source_sha256']
    assert rec['source_sha256'] in review.read_text(encoding='utf-8-sig').lower(),module
    assert rec['exit_code']==0
    actual = re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",log.read_text(encoding='utf-8'))
    assert len(actual)==len(rec['reports'])
    for (name,axioms),report in zip(actual,rec['reports']):
        assert name==report['declaration'] and name not in declarations
        assert {s.strip() for s in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
        declarations.add(name)
    records.append(dict(module=module,reports=len(rec['reports']),source_sha256=rec['source_sha256'],
        audit_log=rec['log'],audit_log_sha256=rec['log_sha256'],independent_review=rel(review),
        independent_review_sha256=sha(review.read_bytes()),declarations=[r['declaration'] for r in rec['reports']]))
assert len(declarations)==102
ledger = prior+records
assert ledger[:503]==prior
ledger_path = evidence/'audited_after_5238-stage67.json'
write(ledger_path,ledger)
for module,rec in prov['modules'].items():
    assert sha((root/rec['path']).read_bytes())==rec['sha256'],module
files = {root/r['source'] for r in chain['records']}
files.update(root/r['log'] for r in chain['records'])
files.update(checkpoint/'reviews'/x for x in reviews.values())
files.update((checkpoint/'reviews').glob('*.log'))
files.update(checkpoint.glob('*.log'))
files.update((checkpoint/'scripts').glob('*.py'))
files.update((checkpoint/'scripts').glob('*.ps1'))
files.update([evidence/'chain-build.json',checkpoint/'provenance-audit.json',ledger_path,
    checkpoint/'modules.json',checkpoint/'STAGE67.txt',checkpoint/'START.txt',root/'RESUME.md'])
manifest_files = [dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive = evidence/'stage67-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files):
        z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
    for item in manifest_files:
        assert sha(z.read(item['path']))==item['sha256']
summary = dict(date='2026-11-12',previous_proof_checkpoint='8160201',
    starting_handoff_commit='b54a1e4',intermediate_foundation_commit='6f35912',
    modules=len(ledger),reports=sum(r['reports'] for r in ledger),new_modules=24,new_reports=102,
    all_previous_records_unchanged=True,prior_ledger_sha256=sha(prior_path.read_bytes()),
    ledger_sha256=sha(ledger_path.read_bytes()),source_provenance_sha256=sha((checkpoint/'provenance-audit.json').read_bytes()),
    chain_build_sha256=sha((evidence/'chain-build.json').read_bytes()),
    raw_archive_sha256=sha(archive.read_bytes()),records=records,files=manifest_files,
    scope='Complete Packet02 actual magnetic symmetry and vanishing chain: every complex frequency, all positive real sphere radii, L2 Debye zero. Fresh isolated objects for 24 modules; 485 frozen upstream source dependencies authenticated, cached upstream objects. Not a clean full-project rebuild or full OQ14 closure.')
assert summary['modules']==527 and summary['reports']==3756
write(evidence/'stage67.json',summary)
write(root/'tmp/audited_after_5238.json',ledger)
print('Stage67 frozen: 527 modules / 3756 reports; +24 / +102; 503 prior records unchanged.')

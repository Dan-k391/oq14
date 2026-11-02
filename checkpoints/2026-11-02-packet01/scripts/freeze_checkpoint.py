"""Validate existing final evidence and freeze the stage-66 incremental ledger."""
from pathlib import Path
import hashlib
import json
import re
import zipfile

checkpoint = Path(__file__).resolve().parent.parent
root = checkpoint.parent.parent
evidence = checkpoint / 'evidence'
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
rel = lambda p: p.relative_to(root).as_posix()
write = lambda p, v: p.write_text(json.dumps(v, indent=2)+'\n', encoding='utf-8', newline='\n')
chain = load(evidence / 'chain-build.json')
assert chain['complete'] and chain['module_count'] == 8 and chain['report_count'] == 22
prov = load(checkpoint / 'provenance-audit.json')
assert prov['counts'] == {'matched': 302, 'new_or_pending': 8}
assert not prov['missing_roots']
prior_path = root / 'checkpoints/2026-10-27-continuation/evidence/audit-metadata/audited_after_5238-stage65.json'
prior = load(prior_path)
assert len(prior) == 495 and sum(r['reports'] for r in prior) == 3632
reviews = {
    'KernelRadialMomentBridge': 'MonopoleChain-root.txt',
    'MonopoleFlux': 'MonopoleChain-root.txt',
    'Packet01Monopole': 'MonopoleChain-root.txt',
    'Packet01MomentIntegrability': 'MomentIntegrability-root.txt',
    'Packet01RadialTestReduction': 'Packet01RadialTestReduction.review.txt',
    'Packet01WeakDerivative': 'Packet01WeakDerivative-independent.txt',
    'Packet01PoloidalCoefficients': 'Packet01PoloidalCoefficients-independent.txt',
    'Packet01CoefficientChain': 'Packet01CoefficientChain-independent.txt',
}
old_names = {r['module'] for r in prior}
records = []
declarations = set()
for rec in chain['records']:
    module = rec['module']
    assert module not in old_names
    source = root / rec['source']
    log = root / rec['log']
    review = checkpoint / 'reviews' / reviews[module]
    assert sha(source.read_bytes()) == rec['source_sha256']
    assert sha(log.read_bytes()) == rec['log_sha256']
    assert prov['modules'][module]['sha256'] == rec['source_sha256']
    assert rec['exit_code'] == 0
    actual = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text(encoding='utf-8'))
    assert len(actual) == len(rec['reports'])
    for (name, axioms), report in zip(actual, rec['reports']):
        assert name == report['declaration'] and name not in declarations
        assert {s.strip() for s in axioms.split(',')} <= {'propext','Classical.choice','Quot.sound'}
        declarations.add(name)
    if 'independent' in review.name or module == 'Packet01RadialTestReduction':
        assert rec['source_sha256'] in review.read_text(encoding='utf-8-sig').lower()
    records.append(dict(module=module, reports=len(rec['reports']),
        source_sha256=rec['source_sha256'], audit_log=rec['log'],
        audit_log_sha256=rec['log_sha256'], independent_review=rel(review),
        independent_review_sha256=sha(review.read_bytes()),
        declarations=[r['declaration'] for r in rec['reports']]))
assert len(declarations) == 22
ledger = prior + records
assert ledger[:495] == prior
ledger_path = evidence / 'audited_after_5238-stage66.json'
write(ledger_path, ledger)

# Recheck every upstream source against the already authenticated audit.
for module, rec in prov['modules'].items():
    assert sha((root / rec['path']).read_bytes()) == rec['sha256'], module
files = set(root / r['source'] for r in chain['records'])
files.update(root / r['log'] for r in chain['records'])
files.update(checkpoint / 'reviews' / x for x in reviews.values())
files.update([evidence / 'chain-build.json', checkpoint / 'provenance-audit.json', ledger_path,
              checkpoint / 'STAGE66.txt', checkpoint / 'START.txt'])
files.update((checkpoint / 'scripts').glob('*'))
# Preserve cited independent compiler outputs, including the older successful
# targeted logs retained in the textual review histories.
files.update(checkpoint.glob('*independent*.log'))
files.add(evidence / 'Packet01RadialTestReduction.audit.log')
manifest_files = [dict(path=rel(p), sha256=sha(p.read_bytes())) for p in sorted(files)]
archive = evidence / 'stage66-raw-evidence.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files):
        z.write(p, rel(p))
with zipfile.ZipFile(archive) as z:
    for item in manifest_files:
        assert sha(z.read(item['path'])) == item['sha256']
summary = dict(date='2026-11-02', previous_proof_checkpoint='aeed697d5224424878d99840d33b67abde175947',
    starting_handoff_commit='ff15b1e', intermediate_monopole_commit='ea946c2',
    modules=len(ledger), reports=sum(r['reports'] for r in ledger), new_modules=8, new_reports=22,
    all_previous_records_unchanged=True, prior_ledger_sha256=sha(prior_path.read_bytes()),
    ledger_sha256=sha(ledger_path.read_bytes()), source_provenance_sha256=sha((checkpoint/'provenance-audit.json').read_bytes()),
    chain_build_sha256=sha((evidence/'chain-build.json').read_bytes()),
    raw_archive_sha256=sha(archive.read_bytes()), records=records, files=manifest_files,
    scope='Complete new Packet01 chain compiled in isolated objects and independently reviewed; 302 upstream source dependencies authenticated. No full-project clean rebuild or full OQ14 closure.')
assert summary['modules'] == 503 and summary['reports'] == 3654
write(evidence / 'stage66.json', summary)
print('Stage66 frozen: 503 modules / 3654 reports; +8 / +22; 495 prior records unchanged.')

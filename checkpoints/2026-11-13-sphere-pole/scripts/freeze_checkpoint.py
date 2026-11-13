"""Validate and archive stage71, including the exact independent review boundaries."""
from pathlib import Path
import hashlib, json, re, zipfile
cp = Path(__file__).resolve().parent.parent
root = cp.parent.parent
ev = cp/'evidence'
reviews = cp/'reviews'
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda b: hashlib.sha256(b).hexdigest()
rel = lambda p: p.relative_to(root).as_posix()
write = lambda p,v: p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
pp = cp/'provenance-audit.json'
pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
chain = load(ev/'chain-build.json')
assert chain['complete'] and chain['module_count']==14 and chain['report_count']==72
prov = load(pp)
assert prov['counts']=={'matched':689,'new_or_pending':14} and not prov['missing_roots']
prior_path = root/'checkpoints/2026-11-13-full-channel/evidence/audited_after_5238-stage70.json'
prior = load(prior_path)
assert len(prior)==576 and sum(r['reports'] for r in prior)==3977
independent = {}
for name,review in [('independent-build.json','independent-review.txt')]:
    build = load(reviews/name)
    assert build['complete']
    for r in build['records']:
        independent[r['module']] = (r,reviews/review,reviews/name)
assert len(independent)==9
records = []
allowed = {'propext','Classical.choice','Quot.sound'}
for r in chain['records']:
    m = r['module']; src = root/r['source']; log = root/r['log']
    assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']
    assert sha(log.read_bytes())==r['log_sha256'] and r['exit_code']==0
    assert sha((root/chain['object_directory']/(m+'.olean')).read_bytes())==r['object_sha256']
    logs = [log]
    if m in independent:
        ir,review,ibuild = independent[m]
        ilog = reviews/(m+'-independent.log')
        assert ir['source_sha256']==r['source_sha256'] and ir['exit_code']==0
        assert ir['reports']==len(r['reports']) and ir['log_sha256']==sha(ilog.read_bytes())
        logs.append(ilog)
        mode = 'Terra source review and separate fresh compilation of root-authored module'
    else:
        review = reviews/'root-actual-review.txt'
        ibuild = ev/'chain-build.json'
        ilog = log
        assert r['source_sha256'] in review.read_text(encoding='utf-8')
        mode = 'Root source review and fresh chain compilation, independent of Terra author'
    for p in logs:
        output = p.read_text(encoding='utf-8')
        assert 'error:' not in output and 'warning:' not in output
        parsed = re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",output)
        assert [n for n,_ in parsed]==[x['declaration'] for x in r['reports']]
        for name,axs in parsed:
            assert {x.strip() for x in axs.split(',') if x.strip()}<=allowed
    records.append(dict(module=m,reports=len(r['reports']),source_sha256=r['source_sha256'],
        audit_log=r['log'],audit_log_sha256=r['log_sha256'],independent_review=rel(review),
        independent_review_sha256=sha(review.read_bytes()),independent_review_mode=mode,
        independent_build=rel(ibuild),independent_build_sha256=sha(ibuild.read_bytes()),
        independent_log=rel(ilog),independent_log_sha256=sha(ilog.read_bytes()),
        declarations=[x['declaration'] for x in r['reports']]))
assert not ({r['module'] for r in records}&{r['module'] for r in prior})
ledger = prior+records
assert len(ledger)==590 and sum(r['reports'] for r in ledger)==4049 and ledger[:576]==prior
ledger_path = ev/'audited_after_5238-stage71.json'; write(ledger_path,ledger)
for m,r in prov['modules'].items():
    assert sha((root/r['path']).read_bytes())==r['sha256'],m
files = {root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
files.update(p for p in reviews.iterdir() if p.is_file())
files.update(p for p in (cp/'scripts').iterdir() if p.is_file())
files.update([ev/'chain-build.json',ledger_path,cp/'modules.json',pp,
              cp/'STAGE71.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest = [dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive = ev/'stage71-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files): z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
    for r in manifest: assert sha(z.read(r['path']))==r['sha256']
summary = dict(date='2026-11-13',previous_proof_checkpoint='f9232d3',
    modules=590,reports=4049,
    new_modules=14,new_reports=72,all_previous_records_unchanged=True,
    prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(ledger_path.read_bytes()),
    source_provenance_sha256=sha(pp.read_bytes()),
    chain_build_sha256=sha((ev/'chain-build.json').read_bytes()),raw_archive_sha256=sha(archive.read_bytes()),
    records=records,files=manifest,
    scope='Actual sphere inverse simple pole, rank-one residue, analytic regular part, closed range/cokernel one, exact physical pairing and reciprocal normalization, local observation and weighted transport. 14 fresh isolated objects; 689 authenticated upstream sources with cached objects. Full OQ14 remains active and incomplete.')
write(ev/'stage71.json',summary); write(root/'tmp/audited_after_5238.json',ledger)
print('Stage69 frozen: 559 modules / 3890 reports; +26 / +105; 533 prior records unchanged.')

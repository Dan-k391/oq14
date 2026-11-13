"""Validate and archive the immutable stage68 vector-chain evidence."""
from pathlib import Path
import hashlib, json, re, shutil, zipfile
cp=Path(__file__).resolve().parent.parent
root=cp.parent.parent
ev=cp/'evidence'
pp=cp/'provenance-audit.json'
pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
chain=load(ev/'chain-build.json')
assert chain['complete'] and chain['module_count']==6 and chain['report_count']==29
prov=load(cp/'provenance-audit.json')
assert prov['counts']=={'matched':506,'new_or_pending':6} and not prov['missing_roots']
prior_path=root/'checkpoints/2026-11-12-packet02/evidence/audited_after_5238-stage67.json'
prior=load(prior_path)
assert len(prior)==527 and sum(r['reports'] for r in prior)==3756
reviews=cp/'reviews'; reviews.mkdir(exist_ok=True)
src_reviews=root/'checkpoints/2026-11-12-full-closure/reviews'
review=reviews/'six-module-review.md'
shutil.copyfile(src_reviews/review.name,review)
review.write_text(review.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
records=[]
for r in chain['records']:
    m=r['module']; src=root/r['source']; log=root/r['log']
    assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']
    assert sha(log.read_bytes())==r['log_sha256'] and r['exit_code']==0
    assert r['source_sha256'] in review.read_text(encoding='utf-8')
    independent=reviews/f'{m}-independent.log'
    shutil.copyfile(src_reviews/independent.name,independent)
    for p in [log,independent]:
        text=p.read_text(encoding='utf-8')
        assert 'error:' not in text and 'warning:' not in text
        reports=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",text)
        assert [x[0] for x in reports]==[x['declaration'] for x in r['reports']]
        for name,axs in reports:
            assert {x.strip() for x in axs.split(',')}<={'propext','Classical.choice','Quot.sound'}
    records.append(dict(module=m,reports=len(r['reports']),source_sha256=r['source_sha256'],
        audit_log=r['log'],audit_log_sha256=r['log_sha256'],independent_review=rel(review),
        independent_review_sha256=sha(review.read_bytes()),
        declarations=[x['declaration'] for x in r['reports']]))
assert not ({r['module'] for r in records}&{r['module'] for r in prior})
ledger=prior+records
assert len(ledger)==533 and sum(r['reports'] for r in ledger)==3785 and ledger[:527]==prior
ledger_path=ev/'audited_after_5238-stage68.json'; write(ledger_path,ledger)
for m,r in prov['modules'].items():
    assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
files.update(reviews.iterdir()); files.update((cp/'scripts').iterdir())
files.update([ev/'chain-build.json',ledger_path,cp/'modules.json',cp/'provenance-audit.json',
              cp/'STAGE68.txt',root/'RESUME.md'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage68-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files):z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
    for r in manifest:assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-12',previous_proof_checkpoint='36a2f98',modules=533,reports=3785,
    new_modules=6,new_reports=29,all_previous_records_unchanged=True,
    prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(ledger_path.read_bytes()),
    source_provenance_sha256=sha((cp/'provenance-audit.json').read_bytes()),
    chain_build_sha256=sha((ev/'chain-build.json').read_bytes()),raw_archive_sha256=sha(archive.read_bytes()),
    records=records,files=manifest,
    scope='Actual weak sphere Maxwell, vector angular separation, and electric toroidal zero ae in radius. Six fresh isolated module objects; 506 authenticated upstream sources, cached upstream objects. Full OQ14 closure remains active and incomplete.')
write(ev/'stage68.json',summary);write(root/'tmp/audited_after_5238.json',ledger)
print('Stage68 frozen: 533 modules / 3785 reports; +6 / +29; 527 prior records unchanged.')

"""Freeze independently reviewed flat-interface continuity evidence.

Run after the stage marker and review have been finalized. This script never
changes RESUME.md or the shared temporary ledger; checkpoint owner may promote
its resulting ledger after independent inspection.
"""
from pathlib import Path
import hashlib, json, re, zipfile
cp=Path(__file__).resolve().parent.parent; root=cp.parent.parent; ev=cp/'evidence'
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
prov=load(cp/'provenance-audit.json')
assert prov['counts']=={'matched':120,'new_or_pending':8} and not prov['missing_roots']
assert not any(v['status'] in ('unlisted','hash_mismatch') for v in prov['modules'].values())
chain=load(ev/'chain-build.json'); assert chain['complete'] and chain['module_count']==8 and chain['report_count']==22
prior_path=root/'checkpoints/2026-11-13-driven-components/evidence/audited_after_5238-stage75.json'
prior=load(prior_path); assert len(prior)==673 and sum(r['reports'] for r in prior)==4290
review_path=cp/'reviews/review-manifest.json'; review=load(review_path)
assert review['status']=='pass' and review['total_reports']==22
reviews={r['module']:r for r in review['modules']}
new=[]; allowed={'propext','Classical.choice','Quot.sound'}
for r in chain['records']:
 m=r['module']; src=root/r['source']; log=root/r['log']; rr=reviews[m]
 assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']==rr['source_sha256']
 assert r['exit_code']==0 and sha(log.read_bytes())==r['log_sha256']
 assert sha((root/chain['object_directory']/(m+'.olean')).read_bytes())==r['object_sha256']
 raw=(cp/'reviews'/(m+'.log')).read_bytes(); assert sha(raw)==rr['isolated_log_sha256']
 s=log.read_text(encoding='utf-8'); assert not re.search(r'warning:|error:|sorryAx',s)
 reports=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",s)
 assert [n for n,a in reports]==[x['declaration'] for x in r['reports']]
 for n,a in reports: assert {x.strip() for x in a.split(',') if x.strip()}<=allowed
 new.append(dict(module=m,reports=len(reports),source_sha256=r['source_sha256'],
  audit_log=r['log'],audit_log_sha256=r['log_sha256'],
  independent_review=rel(review_path),independent_review_sha256=sha(review_path.read_bytes()),
  independent_review_mode='Independent semantic review and separate isolated ordered rebuild',
  independent_build=rel(cp/'reviews/rebuild.ps1'),
  independent_build_sha256=sha((cp/'reviews/rebuild.ps1').read_bytes()),
  independent_log=rel(cp/'reviews'/(m+'.log')),independent_log_sha256=sha(raw),
  declarations=[n for n,a in reports]))
assert not ({r['module'] for r in prior}&{r['module'] for r in new})
ledger=prior+new; assert len(ledger)==681 and sum(r['reports'] for r in ledger)==4312 and ledger[:673]==prior
lp=ev/'audited_after_5238-stage76.json'; write(lp,ledger)
for m,r in prov['modules'].items(): assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
for folder in [cp/'scripts',cp/'reviews']: files.update(p for p in folder.iterdir() if p.is_file())
files.update([lp,cp/'provenance-audit.json',ev/'chain-build.json',cp/'modules.json',cp/'STAGE76.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage76-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files): z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest: assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='bc28631',modules=681,reports=4312,
 new_modules=8,new_reports=22,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(lp.read_bytes()),
 raw_archive_sha256=sha(archive.read_bytes()),records=new,files=manifest,
 scope='Flat-interface weak-Maxwell a.e. one-sided continuity and attained two-branch maximum; no curved-interface conclusion. Full OQ14 remains active and incomplete.')
write(ev/'stage76.json',summary)
print('Stage76 verified: 681 modules / 4312 reports; +8 / +22; 673 prior records unchanged. Shared ledger untouched.')

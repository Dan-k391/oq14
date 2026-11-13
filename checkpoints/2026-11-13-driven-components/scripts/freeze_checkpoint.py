"""Freeze independently rebuilt exact driven connected-component construction."""
from pathlib import Path
import hashlib,json,re,zipfile
cp=Path(__file__).resolve().parent.parent; root=cp.parent.parent; ev=cp/'evidence'
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
pp=cp/'provenance-audit.json'; pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
prov=load(pp); assert prov['counts']=={'matched':807,'new_or_pending':16} and not prov['missing_roots']
chain=load(ev/'chain-build.json'); assert chain['complete'] and chain['module_count']==16 and chain['report_count']==32
prior_path=root/'checkpoints/2026-11-13-modal-transport/evidence/audited_after_5238-stage74.json'
prior=load(prior_path); assert len(prior)==657 and sum(r['reports'] for r in prior)==4258
review=cp/'reviews/root-review.txt'; normal={r['module']:r for r in load(cp/'reviews/normalization.json')}
new=[]; allowed={'propext','Classical.choice','Quot.sound'}
for r in chain['records']:
 m=r['module']; src=root/r['source']; log=root/r['log']
 assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']==normal[m]['normalized_sha256']
 assert r['source_sha256'] in review.read_text(encoding='utf-8')
 assert r['exit_code']==0 and sha(log.read_bytes())==r['log_sha256']
 assert sha((root/chain['object_directory']/(m+'.olean')).read_bytes())==r['object_sha256']
 s=log.read_text(encoding='utf-8'); assert 'warning:' not in s and 'error:' not in s
 reports=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",s)
 assert [n for n,a in reports]==[x['declaration'] for x in r['reports']]
 for n,a in reports: assert {x.strip() for x in a.split(',') if x.strip()}<=allowed
 new.append(dict(module=m,reports=len(reports),source_sha256=r['source_sha256'],
  audit_log=r['log'],audit_log_sha256=r['log_sha256'],
  independent_review=rel(review),independent_review_sha256=sha(review.read_bytes()),
  independent_review_mode='Root semantic review and independent ordered fresh-object build of Terra sources',
  independent_build=rel(ev/'chain-build.json'),independent_build_sha256=sha((ev/'chain-build.json').read_bytes()),
  independent_log=r['log'],independent_log_sha256=r['log_sha256'],declarations=[n for n,a in reports]))
assert not ({r['module'] for r in prior}&{r['module'] for r in new})
ledger=prior+new; assert len(ledger)==673 and sum(r['reports'] for r in ledger)==4290 and ledger[:657]==prior
lp=ev/'audited_after_5238-stage75.json'; write(lp,ledger)
for m,r in prov['modules'].items(): assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
for folder in [cp/'scripts',cp/'reviews']: files.update(p for p in folder.iterdir() if p.is_file())
files.update([lp,pp,ev/'chain-build.json',cp/'modules.json',cp/'STAGE75.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage75-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files): z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest: assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='ebf68ac',modules=673,reports=4290,
 new_modules=16,new_reports=32,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(lp.read_bytes()),
 raw_archive_sha256=sha(archive.read_bytes()),records=new,files=manifest,
 scope='Exactly 2N connected inclusions in the same actual fixed-frequency driven binary peak device, with unique labels. No attained maxima/collars or radiation completion. Full OQ14 active and incomplete.')
write(ev/'stage75.json',summary); write(root/'tmp/audited_after_5238.json',ledger)
print('Stage75 frozen: 673 modules / 4290 reports; +16 / +32; 657 prior records unchanged.')

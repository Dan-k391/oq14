"""Validate independent reviews, fresh objects, source provenance and stage85 archive."""
from pathlib import Path
import hashlib,json,re,zipfile
cp=Path(__file__).resolve().parent.parent; root=cp.parent.parent; ev=cp/'evidence'; rv=cp/'reviews'
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
pp=cp/'provenance-audit.json'; pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
prov=load(pp); assert prov['counts']=={'matched':1042,'new_or_pending':7} and not prov['missing_roots']
chain=load(ev/'chain-build.json'); assert chain['complete'] and chain['module_count']==7 and chain['report_count']==12
prior_path=root/'checkpoints/2026-11-13-angular-convergence/evidence/audited_after_5238-stage84.json'
prior=load(prior_path); assert len(prior)==787 and sum(r['reports'] for r in prior)==4570
independent={}
b=load(rv/'review-manifest.json'); assert b['status']=='pass_with_scope_caveat'
b['reports']=b['total_reports']
independent[b['module']]=(b,rv/'review-manifest.json',rv/'semantic-review.md',rv/(b['module']+'.log'))
b=load(rv/'certified-review-manifest.json'); assert b['status']=='pass'
for r in b['modules']:
 prefix='sphere-' if r['module'] in ['Packet06CertifiedSphere','Packet06CertifiedInsertion'] else 'certified-'
 independent[r['module']]=(r,rv/'certified-review-manifest.json',rv/'certified-semantic-review.md',rv/(prefix+r['module']+'.log'))
assert len(independent)==7
author={}
new=[]; allowed={'propext','Classical.choice','Quot.sound'}
for r in chain['records']:
 m=r['module']; src=root/r['source']; log=root/r['log']
 assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']
 assert r['exit_code']==0 and sha(log.read_bytes())==r['log_sha256']
 assert sha((root/chain['object_directory']/(m+'.olean')).read_bytes())==r['object_sha256']
 logs=[log]
 if m in independent:
  ir,ib,review,il=independent[m]
  assert ir['source_sha256']==r['source_sha256'] and ir.get('exit_code',0)==0
  assert ir['reports']==len(r['reports']) and sha(il.read_bytes())==ir['log_sha256']
  logs.append(il); mode='Independent Terra source review and separate fresh-object build of root module'
 else:
  assert author[m]['source_sha256']==r['source_sha256']
  review=rv/'root-actual-review.txt'; ib=ev/'chain-build.json'; il=log
  assert r['source_sha256'] in review.read_text(encoding='utf-8')
  mode='Root semantic review and ordered fresh-object compilation of Terra module'
 for p in logs:
  raw=p.read_bytes(); s=raw.decode('utf-16' if raw.startswith((b'\xff\xfe',b'\xfe\xff')) else 'utf-8')
  assert 'warning:' not in s and 'error:' not in s
  reports=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",s)
  assert [n for n,_ in reports]==[x['declaration'] for x in r['reports']]
  for n,a in reports: assert {x.strip() for x in a.split(',') if x.strip()}<=allowed
 new.append(dict(module=m,reports=len(r['reports']),source_sha256=r['source_sha256'],
  audit_log=r['log'],audit_log_sha256=r['log_sha256'],
  independent_review=rel(review),independent_review_sha256=sha(review.read_bytes()),independent_review_mode=mode,
  independent_build=rel(ib),independent_build_sha256=sha(ib.read_bytes()),
  independent_log=rel(il),independent_log_sha256=sha(il.read_bytes()),
  declarations=[x['declaration'] for x in r['reports']]))
assert not ({r['module'] for r in prior}&{r['module'] for r in new})
ledger=prior+new; assert len(ledger)==794 and sum(r['reports'] for r in ledger)==4582 and ledger[:787]==prior
lp=ev/'audited_after_5238-stage85.json'; write(lp,ledger)
for m,r in prov['modules'].items():assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
for folder in [cp/'scripts',rv]:files.update(p for p in folder.iterdir() if p.is_file())
files.update([lp,pp,ev/'chain-build.json',cp/'modules.json',cp/'STAGE85.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage85-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest:assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='4e32a69',modules=794,reports=4582,
 new_modules=7,new_reports=12,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(lp.read_bytes()),raw_archive_sha256=sha(archive.read_bytes()),
 records=new,files=manifest,
 scope='Actual physical unit high-Q insertion modes with convergent fields and selected-sector observed poles retain a reusable actual kernel/simple Schur certificate for subsequent perturbations. A separate corollary permits arbitrarily small strictly positive profile amplitude. Full OQ14 remains active; actual conical excitation and attained hotspots remain incomplete.')
write(ev/'stage85.json',summary);write(root/'tmp/audited_after_5238.json',ledger)
print('Stage85 frozen: 794 modules / 4582 reports; +7 / +12; 787 prior records unchanged.')

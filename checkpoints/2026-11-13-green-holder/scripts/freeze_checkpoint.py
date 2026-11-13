"""Validate independent reviews, fresh objects, source provenance and stage91 archive."""
from pathlib import Path
import hashlib,json,re,zipfile
cp=Path(__file__).resolve().parent.parent; root=cp.parent.parent; ev=cp/'evidence'; rv=cp/'reviews'
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
pp=cp/'provenance-audit.json'; pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
prov=load(pp); assert prov['counts']=={'matched': 999, 'new_or_pending': 13} and not prov['missing_roots']
chain=load(ev/'chain-build.json'); assert chain['complete'] and chain['module_count']==13 and chain['report_count']==29
prior_path=root/'checkpoints/2026-11-13-sphere-excitation/evidence/audited_after_5238-stage90.json'
prior=load(prior_path); assert len(prior)==845 and sum(r['reports'] for r in prior)==4696
independent={}
author={r['module']:r for r in load(rv/'author-inventory.json')['modules']}; assert len(author)==13
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
ledger=prior+new; assert len(ledger)==858 and sum(r['reports'] for r in ledger)==4725 and ledger[:845]==prior
lp=ev/'audited_after_5238-stage91.json'; write(lp,ledger)
for m,r in prov['modules'].items():assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
for folder in [cp/'scripts',rv]:files.update(p for p in folder.iterdir() if p.is_file())
files.update([lp,pp,ev/'chain-build.json',cp/'modules.json',cp/'STAGE91.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage91-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest:assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='8f06fc2',modules=858,reports=4725,
 new_modules=13,new_reports=29,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(lp.read_bytes()),raw_archive_sha256=sha(archive.read_bytes()),
 records=new,files=manifest,
 scope='actual Green correction Holder estimate. Full OQ14 remains active; actual excitation and attained hotspots are not closed.')
write(ev/'stage91.json',summary);write(root/'tmp/audited_after_5238.json',ledger)
print('Stage91 frozen: 858 modules / 4725 reports; +13 / +29; 845 prior records unchanged.')

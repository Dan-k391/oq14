"""Authenticate and archive the actual flat-interface H2 checkpoint."""
from pathlib import Path
import json,hashlib,re,zipfile
cp=Path(__file__).resolve().parent.parent; root=cp.parent.parent
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
ev=cp/'evidence'; reviews=cp/'reviews'; pp=cp/'provenance-audit.json'
pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
prov=load(pp); assert prov['counts']=={'new_or_pending':34,'matched':98} and not prov['missing_roots']
author=load(cp/'author/manifest.json'); ind=load(reviews/'independent-build.json')
assert ind['complete'] and len(ind['records'])==34 and ind['audit']['exit_code']==0
audit=reviews/'Packet05IndependentAudit.log'; audit_source=reviews/'Packet05IndependentAudit.lean'
assert sha(audit.read_bytes())==ind['audit']['log_sha256']
assert sha(audit_source.read_bytes())==ind['audit']['source_sha256']
allowed={'propext','Classical.choice','Quot.sound'}
def parse(p):
 s=p.read_text(encoding='utf-8'); assert 'warning:' not in s and 'error:' not in s
 result=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",s)
 for n,a in result: assert {x.strip() for x in a.split(',') if x.strip()}<=allowed,(n,a)
 return [n for n,a in result]
names=parse(audit)
assert names==[n for r in author['records'] for n in r['theorems']] and len(names)==106
prior_path=root/'checkpoints/2026-11-13-sphere-pole/evidence/audited_after_5238-stage71.json'
prior=load(prior_path); assert len(prior)==590 and sum(r['reports'] for r in prior)==4049
new=[]
for ar,ir in zip(author['records'],ind['records'],strict=True):
 m=ar['module']; assert ir['module']==m and ir['exit_code']==0
 src=root/'lean'/(m+'.lean'); log=reviews/(m+'.log'); alog=cp/'author'/(m+'.log')
 assert sha(src.read_bytes())==ar['source_sha256']==ir['source_sha256']==prov['modules'][m]['sha256']
 assert sha(log.read_bytes())==ir['log_sha256'] and sha(alog.read_bytes())==ar['log_sha256']
 assert sha((reviews/'fresh-objects'/(m+'.olean')).read_bytes())==ir['object_sha256']
 assert set(parse(log))<=set(ar['theorems']) and set(parse(alog))<=set(ar['theorems'])
 data=src.read_text(encoding='utf-8'); assert not re.search(r'\b(sorry|admit)\b|^\s*(axiom|constant)\s',data,re.M)
 ns=re.findall(r'^namespace (\S+)',data,re.M); assert len(ns)==1
 declared=[ns[0]+'.'+n for n in re.findall(r'^\s*(?:theorem|lemma)\s+(\S+)',data,re.M)]
 assert set(declared)==set(ar['theorems']),m
 new.append(dict(module=m,reports=len(ar['theorems']),source_sha256=ir['source_sha256'],
  audit_log=rel(audit),audit_log_sha256=sha(audit.read_bytes()),
  independent_review=rel(reviews/'independent-review.txt'),
  independent_review_sha256=sha((reviews/'independent-review.txt').read_bytes()),
  independent_review_mode='Terra independent source review and separate ordered fresh-object compilation',
  independent_build=rel(reviews/'independent-build.json'),
  independent_build_sha256=sha((reviews/'independent-build.json').read_bytes()),
  independent_log=rel(log),independent_log_sha256=sha(log.read_bytes()),declarations=ar['theorems']))
assert not ({r['module'] for r in prior}&{r['module'] for r in new})
ledger=prior+new; assert len(ledger)==624 and sum(r['reports'] for r in ledger)==4155 and ledger[:590]==prior
lp=ev/'audited_after_5238-stage72.json'; write(lp,ledger)
for m,r in prov['modules'].items(): assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/'lean'/(r['module']+'.lean') for r in new}
for folder in [reviews,cp/'author',cp/'scripts']: files.update(p for p in folder.iterdir() if p.is_file())
files.update([lp,pp,cp/'modules.json',cp/'STAGE72.txt',root/'RESUME.md',cp/'.gitignore',cp/'.gitattributes'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage72-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files): z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest: assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='a936671',modules=624,reports=4155,
 new_modules=34,new_reports=106,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(lp.read_bytes()),
 raw_archive_sha256=sha(archive.read_bytes()),records=new,files=manifest,
 scope='Actual real-frequency flat-interface phasewise H2. 34 fresh isolated module objects, 106 audited declarations, 98 authenticated upstream local sources with cached objects. Full OQ14 remains active and incomplete.')
write(ev/'stage72.json',summary); write(root/'tmp/audited_after_5238.json',ledger)
print('Stage72 frozen: 624 modules / 4155 reports; +34 / +106; 590 prior records unchanged.')

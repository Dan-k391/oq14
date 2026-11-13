"""Validate and archive independently reviewed full-channel stage70."""
from pathlib import Path
import hashlib,json,re,zipfile
cp=Path(__file__).resolve().parent.parent
root=cp.parent.parent; ev=cp/'evidence'
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
rel=lambda p:p.relative_to(root).as_posix()
write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8',newline='\n')
pp=cp/'provenance-audit.json'
pp.write_text(pp.read_text(encoding='utf-8-sig'),encoding='utf-8',newline='\n')
chain=load(ev/'chain-build.json'); prov=load(pp)
assert chain['complete'] and chain['module_count']==17 and chain['report_count']==87
assert prov['counts']=={'matched':791,'new_or_pending':17} and not prov['missing_roots']
prior_path=root/'checkpoints/2026-11-13-sphere-classification/evidence/audited_after_5238-stage69.json'
prior=load(prior_path)
assert len(prior)==559 and sum(r['reports'] for r in prior)==3890
review=cp/'reviews/root-independent-review.txt'
author={r['module']:r for r in load(cp/'author-inventory.json')}
records=[]
for r in chain['records']:
 m=r['module']; src=root/r['source']; log=root/r['log']
 assert sha(src.read_bytes())==r['source_sha256']==prov['modules'][m]['sha256']==author[m]['frozen_source_sha256']
 assert r['source_sha256'] in review.read_text(encoding='utf-8')
 assert sha(log.read_bytes())==r['log_sha256'] and r['exit_code']==0
 assert sha((root/chain['object_directory']/(m+'.olean')).read_bytes())==r['object_sha256']
 output=log.read_text(encoding='utf-8')
 assert 'error:' not in output and 'warning:' not in output
 parsed=re.findall(r"'(.+?)' depends on axioms:\s*\[([^]]*)\]",output)
 assert [n for n,_ in parsed]==[x['declaration'] for x in r['reports']]==author[m]['axiom_audits']
 for n,axs in parsed:
  assert {x.strip() for x in axs.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
 records.append(dict(module=m,reports=len(r['reports']),source_sha256=r['source_sha256'],
  audit_log=r['log'],audit_log_sha256=r['log_sha256'],independent_review=rel(review),
  independent_review_sha256=sha(review.read_bytes()),
  independent_review_mode='Root source review and fresh isolated chain compilation, independent of Terra author',
  declarations=[x['declaration'] for x in r['reports']]))
assert not ({r['module'] for r in records}&{r['module'] for r in prior})
ledger=prior+records
assert len(ledger)==576 and sum(r['reports'] for r in ledger)==3977 and ledger[:559]==prior
ledger_path=ev/'audited_after_5238-stage70.json'; write(ledger_path,ledger)
for m,r in prov['modules'].items(): assert sha((root/r['path']).read_bytes())==r['sha256'],m
files={root/r['source'] for r in chain['records']}|{root/r['log'] for r in chain['records']}
files.update(p for p in (cp/'scripts').iterdir() if p.is_file())
files.update([review,ev/'chain-build.json',ledger_path,cp/'modules.json',pp,cp/'author-inventory.json',
 cp/'STAGE70.txt',cp/'.gitignore',cp/'.gitattributes',root/'RESUME.md'])
manifest=[dict(path=rel(p),sha256=sha(p.read_bytes())) for p in sorted(files)]
archive=ev/'stage70-raw-evidence.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,rel(p))
with zipfile.ZipFile(archive) as z:
 for r in manifest:assert sha(z.read(r['path']))==r['sha256']
summary=dict(date='2026-11-13',previous_proof_checkpoint='586a764',modules=576,reports=3977,
 new_modules=17,new_reports=87,all_previous_records_unchanged=True,
 prior_ledger_sha256=sha(prior_path.read_bytes()),ledger_sha256=sha(ledger_path.read_bytes()),
 source_provenance_sha256=sha(pp.read_bytes()),chain_build_sha256=sha((ev/'chain-build.json').read_bytes()),
 raw_archive_sha256=sha(archive.read_bytes()),records=records,files=manifest,
 scope='Unrestricted all-N physical counted-channel endpoint for delta>eta and full selected outgoing amplitude, actual same-device bounded full-input map and power-preserving Maxwell dilation. 17 fresh isolated objects, 791 authenticated upstream sources with cached objects. Full OQ14 remains incomplete and active.')
write(ev/'stage70.json',summary);write(root/'tmp/audited_after_5238.json',ledger)
print('Stage70 frozen: 576 modules / 3977 reports; +17 / +87; all 559 prior records unchanged.')

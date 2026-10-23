from pathlib import Path
import hashlib,json,re,shutil,subprocess
r=Path('D:/oq14'); cp=r/'checkpoints/2026-10-23-resume'
base='8a4a8bf4abb15d7ae6f2fc0fa4d63758c3c04248'
assert not cp.exists(),'One-time checkpoint; do not rerun.'
def git(*args):return subprocess.check_output(['git',*args],cwd=r,text=True,encoding='utf-8').strip()
assert git('rev-parse','HEAD')==base
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def decode(p):
    b=p.read_bytes();return b.decode('utf-16' if b[:2] in (b'\xff\xfe',b'\xfe\xff') else 'utf-8-sig')
ledger=json.loads((r/'tmp/audited_after_5238.json').read_text(encoding='utf-8'))
assert len(ledger)==169 and sum(v['reports'] for v in ledger)==832
audited={v['module']:v for v in ledger}
paths=set(git('ls-files','--others','--exclude-standard','--','lean','reviews').splitlines())
paths.update(git('diff','--name-only','--','lean','reviews','RESUME.md').splitlines())
paths.add('RESUME.md');paths.discard('')
mods=sorted(Path(p).stem for p in paths if p.endswith('.lean'))
assert len(mods)==180 and set(audited)<=set(mods)
author={
 'CompactCoreKernel':'lean/logs/CompactCoreKernel-check2.log',
 'SourcePairedCore':'lean/logs/SourcePairedCore-check2.log',
 'ConicalUniformBall':'lean/ConicalUniformBall.final.log',
 'FiniteAngularNonzero':'lean/FiniteAngularNonzero.final.log',
 'FiniteMixedFields':'lean/logs/FiniteMixedFields-final.log',
 'SphereVectorPairing':'lean/logs/SphereVectorPairing-final.log',
 'ConicalFixedAngularInput':'lean/ConicalFixedAngularInput-check2.log',
 'RestrictedTEFieldLinear':'lean/logs/RestrictedTEFieldLinear-target.log',
}
module_status=[]
for name in mods:
    p=r/'lean'/f'{name}.lean';src=p.read_text(encoding='utf-8-sig')
    expected=set(re.findall(r'#print axioms (OQ14(?:\.\w+)+)',src))
    flags=re.findall(r'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit)\b',src)
    rec={'module':name,'reports':len(expected),'source_sha256':sha(p),
         'source_lf_sha256':hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
         'source_placeholder_scan_clean':not flags}
    assert not flags,name
    log=None
    if name in audited:
        a=audited[name];assert rec['source_sha256']==a['source_sha256'],name
        log=r/a['audit_log'];assert sha(log)==a['audit_log_sha256'],name
        rec['status']='INDEPENDENT PASS';rec['independent_receipt']=a
    elif name in author:
        log=r/author[name]
        rec['status']=('TARGET PASS; NO FINAL OBJECT' if name=='ConicalFixedAngularInput' else
            'TARGET PASS WITH OBJECT; INDEPENDENT AUDIT PENDING' if name=='RestrictedTEFieldLinear' else
            'AUTHOR PASS; INDEPENDENT AUDIT PENDING')
    else:
        rec['status']=('UNCOMPILED DRAFT' if name=='MaterialSourceLinear' else 'FAILED DRAFT; SEE HANDOFF')
    if log:
        s=decode(log);assert not re.search(r'warning:|error:|sorryAx',s),name
        found=dict(re.findall(r"'(OQ14(?:\.\w+)+)' depends on axioms: \[([^\]]*)\]",s))
        found.update({n:'' for n in re.findall(r"'(OQ14(?:\.\w+)+)' does not depend on any axioms",s)})
        assert set(found)==expected,name
        assert all({a.strip() for a in axes.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'} for axes in found.values()),name
        rec['log']=log.relative_to(r).as_posix();rec['log_sha256']=sha(log)
    obj=r/'lean/.lake/build/lib/lean'/f'{name}.olean'
    rec['local_object']={'exists':obj.exists(),'bytes':obj.stat().st_size if obj.exists() else None,
        'sha256':sha(obj) if obj.exists() else None,'note':'Local evidence only; does not certify the current source.'}
    if name in author and name!='ConicalFixedAngularInput':assert obj.exists(),name
    module_status.append(rec)
cp.mkdir(parents=True)
(cp/'.gitattributes').write_text('work/** -text\nevidence/** -text\n',encoding='utf-8')
shutil.copy2(r/'checkpoints/2026-10-22-resume/restore-work.ps1',cp/'restore-work.ps1')
work=[];evidence=[]
def copy(src,dst,records,rel):
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
    assert sha(src)==sha(dst)
    records.append({'path':rel,'bytes':dst.stat().st_size,'sha256':sha(dst)})
for rel in sorted(paths):copy(r/rel,cp/'work'/rel,work,rel)
def save(src,rel):copy(src,cp/'evidence'/rel,evidence,'evidence/'+rel)
for folder in [r/'lean/logs',r/'lean']:
    for p in sorted(folder.iterdir()):
        if p.is_file() and p.suffix in ('.log','.txt') and any(p.name.startswith(n+'-') or p.name.startswith(n+'.') for n in mods):
            save(p,'targeted/'+p.relative_to(r/'lean').as_posix())
for name in ['audited_after_5238.json','record_after_5238.py','record_modal_after_5238.py',
             'record_source_converse_stage.py','record_source_physical_stage.py','record_source_tensor_stage.py',
             'create_stop_checkpoint_20261023.py','resume_active_before_stop_20261023.md','clean-5238-release-validation.json']:
    save(r/'tmp'/name,'audit-metadata/'+name)
for rel in ['lean/clean-build.txt','lean/provenance.json','build-manifest.json','verification.json',
            'model-diagnostics.csv','latex-final-pass.log','compiler-output.txt','pdf/oq14-manuscript.pdf',
            'RELEASE.md','SHA256SUMS.json','preservation.json','bundle-verification.txt']:
    save(r/'output/checkpoints/oq14-maxwell-foundations-5238'/rel,'clean-release-5238/'+rel)
handoffs=sorted(p for p in paths if p.startswith('reviews/') and ('stop' in p.lower()) and ('23' in p))
status={'paused':True,'task_complete':False,'user_request':'stop and create checkpoint',
        'active_compiler_jobs':0,'active_agent_jobs':0,'handoffs':handoffs,
        'last_root_compiler':'RestrictedTEDipoleLimit-root-audit EXIT0; session4291 consumed',
        'last_root_author':'SourcePairedCore-check2 EXIT0; session39505 consumed',
        'new_aggregate_build_performed':False}
statusfile=cp/'evidence/build-status.json';statusfile.write_text(json.dumps(status,indent=2)+'\n',encoding='utf-8')
evidence.append({'path':statusfile.relative_to(cp).as_posix(),'bytes':statusfile.stat().st_size,'sha256':sha(statusfile)})
manifest={'checkpoint_tag':'oq14-resume-2026-10-23','user_requested_pause':True,'task_complete':False,
 'registered_base_commit':base,'latest_coherent_release':'oq14-maxwell-foundations-5238',
 'registered_reports':5238,'registered_modules':627,'registered_libraries':599,
 'new_unregistered_modules':len(mods),'new_source_report_directives':sum(v['reports'] for v in module_status),
 'independently_audited_modules':169,'independently_audited_reports':832,
 'active_compiler_jobs':0,'active_agent_jobs':0,'module_status':module_status,
 'saved_working_files':work,'evidence_files':evidence,'handoffs':handoffs}
(cp/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
(cp/'README.md').write_text('''# Paused OQ14 checkpoint — October 23, 2026

Read work/RESUME.md, manifest.json and the three agent handoffs listed there.
Full OQ14 closure is unfinished. The clean5238 release remains unchanged.
This checkpoint preserves180 newer Lean sources, including169 independently
checked modules /832 proof reports and eleven files with newer or draft status.
No active proof agents or Lean compiler jobs remain. Resume only at user request.

Exact working bytes and compiler evidence are hash-checked in manifest.json.
restore-work.ps1 restores explicitly named missing files only; it refuses
overwrites and paths outside this workspace. Git may normalize working source
line endings; exact frozen bytes remain in work/. Recompile restored sources.
Compiler binaries, dependency caches and unrelated sites/ are not included.
''',encoding='utf-8')
for v in work:assert sha(cp/'work'/v['path'])==v['sha256'] and sha(r/v['path'])==v['sha256']
for v in evidence:assert sha(cp/v['path'])==v['sha256']
stage=sorted(paths|{p.relative_to(r).as_posix() for p in cp.rglob('*') if p.is_file()})
assert all(not p.startswith('sites/') for p in stage)
(r/'tmp/checkpoint_20261023_stage.nul').write_bytes(b'\0'.join(p.encode() for p in stage)+b'\0')
print(json.dumps({'checkpoint':str(cp),'work_files':len(work),'evidence_files':len(evidence),
    'modules':len(mods),'reports':manifest['new_source_report_directives'],'verified':True},indent=2))

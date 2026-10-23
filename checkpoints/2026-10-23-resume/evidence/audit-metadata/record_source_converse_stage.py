from pathlib import Path
import hashlib,json,re
root=Path(r'D:\oq14')
checks={
 'RadiatingFieldPower':2,'RadiatingMaxwellUniqueness':2,'RadiatingTrace':1,
 'ForcedMaxwellResponse':1,'RadiatingSourceRepresentation':1,'ForcedTestLocalization':2,
 'SourceRegularCorrection':2,'TestFieldLocalization':2,'SourceRegularNear':1,
 'SourceTestIntegrals':1,'SourcePuncturedCorrection':1,'SourceGlobalCorrection':1,
 'SourceVolumeRepresentation':1,'MaterialVolumeConverse':1,
}
records=[]
for module,check in checks.items():
    source=root/'lean'/f'{module}.lean'
    log=root/'lean/logs'/f'{module}-check{check}.log'
    receipt=log.with_name(log.stem+'.exit.log')
    data=source.read_bytes(); src=data.decode('utf-8-sig')
    raw=log.read_bytes(); txt=raw.decode('utf-16' if raw[:2] in (b'\xff\xfe',b'\xfe\xff') else 'utf-8-sig')
    assert receipt.read_text(encoding='utf-8-sig').strip()=='0',module
    assert not re.search(r'(?m)^\s*(axiom|constant)\s|\b(sorry|admit)\b',src),module
    assert not re.search(r'warning:|error:|sorryAx',txt),module
    names=set(re.findall(r'#print axioms (OQ14(?:\.\w+)+)',src))
    reports=dict(re.findall(r"'(OQ14(?:\.\w+)+)' depends on axioms: \[([^\]]*)\]",txt))
    for name in re.findall(r"'(OQ14(?:\.\w+)+)' does not depend on any axioms",txt):reports[name]=''
    assert names==set(reports),module
    assert all({a.strip() for a in axes.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'} for axes in reports.values()),module
    records.append(dict(module=module,reports=len(names),source_sha256=hashlib.sha256(data).hexdigest(),
        author_log=log.relative_to(root).as_posix(),author_log_sha256=hashlib.sha256(raw).hexdigest()))
dest=root/'reviews/source_maxwell_converse_stage_2026_10_23.json'
if dest.exists():
    assert json.loads(dest.read_text(encoding='utf-8'))==records,'frozen author records changed'
else:dest.write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print(len(records),sum(r['reports'] for r in records),'author proof reports validated')

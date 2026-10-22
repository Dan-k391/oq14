from pathlib import Path
import hashlib,json,re,sys
root=Path(r'D:\oq14')
out=root/'tmp/audited_after_4391.json'
records={v['module']:v for v in json.loads(out.read_text())} if out.exists() else {}
for name in sys.argv[1:]:
    source=root/'lean'/f'{name}.lean'
    log=root/'lean/logs'/f'{name}-root-audit.log'
    receipt=root/'lean/logs'/f'{name}-root-audit.exit.log'
    data=source.read_bytes(); s=data.decode('utf-8-sig')
    raw=log.read_bytes(); text=raw.decode('utf-16' if raw[:2] in (b'\xff\xfe',b'\xfe\xff') else 'utf-8-sig')
    assert receipt.read_text(encoding='utf-8-sig').strip()=='0',name
    assert not re.search(r'(?m)^\s*(axiom|constant)\s|\b(sorry|admit)\b',s),name
    assert not re.search(r'warning:|error:|sorryAx',text),name
    expected=set(re.findall(r'#print axioms (OQ14(?:\.\w+)+)',s))
    reports=dict(re.findall(r"'(OQ14(?:\.\w+)+)' depends on axioms: \[([^\]]*)\]",text))
    for n in re.findall(r"'(OQ14(?:\.\w+)+)' does not depend on any axioms",text): reports[n]=''
    assert expected==set(reports),(name,expected-set(reports))
    for a in reports.values():
        assert {x.strip() for x in a.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
    rec=dict(module=name,reports=len(expected),source_sha256=hashlib.sha256(data).hexdigest(),
        audit_log=log.relative_to(root).as_posix(),audit_log_sha256=hashlib.sha256(raw).hexdigest())
    if name in records: assert records[name]==rec,(name,'changed frozen receipt')
    records[name]=rec
out.write_text(json.dumps(list(records.values()),indent=2)+'\n',encoding='utf-8')
print(len(records),sum(x['reports'] for x in records.values()),'independent checks recorded')

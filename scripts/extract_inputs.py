"""Read-only input audit; produce cached text and hashes, never execute HTML."""
from pathlib import Path
from html.parser import HTMLParser
from hashlib import sha256
import json

ROOT=Path(__file__).resolve().parents[1]
class Text(HTMLParser):
    def __init__(self):
        super().__init__(); self.out=[]; self.skip=0
    def handle_starttag(self, tag, attrs):
        if tag in ('script','style'): self.skip+=1
        if tag in ('h1','h2','h3','h4','p','li','section'): self.out.append('\n')
    def handle_endtag(self, tag):
        if tag in ('script','style'): self.skip-=1
    def handle_data(self, data):
        if not self.skip: self.out.append(data)

records=[]
for name in ('OQ14_Agent_Manual.txt','oq14_research_report.pdf','optical_channel_bounds.pdf','oq14-channel-bounds-standalone.html'):
    p=Path('C:/Users/Daniel/Downloads')/name
    record={'name':name, 'present':p.is_file()}
    if p.is_file():
        b=p.read_bytes(); record.update(bytes=len(b),sha256=sha256(b).hexdigest())
        if p.suffix=='.html':
            parser=Text(); parser.feed(b.decode('utf-8'))
            ROOT.joinpath('sources/cache/prior-html.txt').write_text(''.join(parser.out),encoding='utf-8')
    records.append(record)
p=ROOT/'sources/cache/tutorial.html'
if p.exists():
    parser=Text(); parser.feed(p.read_text(encoding='utf-8'))
    ROOT.joinpath('sources/cache/tutorial.txt').write_text(''.join(parser.out),encoding='utf-8')
ROOT.joinpath('evidence/input-manifest.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print(json.dumps(records,indent=2))

"""Cache public primary sources; cache files are not redistributed or versioned."""
from pathlib import Path
from urllib.request import urlopen, Request
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / 'sources' / 'cache'
SOURCES = {
    'tutorial.html': 'https://arxiv.org/html/2605.24738v1',
    'miller2023.pdf': 'https://dabm.stanford.edu/wp-content/uploads/2023/01/J289.pdf',
    'kuang2025.pdf': 'https://dabm.stanford.edu/wp-content/uploads/2025/06/J298.pdf',
    'costabel1999.pdf': 'https://www.numdam.org/item/M2AN_1999__33_3_627_0.pdf',
    'zhao2020.pdf': 'https://arxiv.org/pdf/2008.13241',
}

def fetch(item):
    name, url = item
    try:
        data = urlopen(Request(url, headers={'User-Agent':'OQ14 research source audit'}), timeout=90).read()
        if name.endswith('.pdf') and not data.startswith(b'%PDF'):
            raise ValueError('Response is not a PDF')
        CACHE.joinpath(name).write_bytes(data)
        if name.endswith('.pdf'):
            from pypdf import PdfReader
            reader = PdfReader(CACHE / name)
            CACHE.joinpath(name+'.txt').write_text('\n\n'.join('PAGE '+str(i+1)+'\n'+(p.extract_text() or '') for i,p in enumerate(reader.pages)), encoding='utf-8')
        return {'file': name, 'url': url, 'sha256': sha256(data).hexdigest(), 'bytes':len(data), 'status':'retrieved'}
    except Exception as exc:
        return {'file':name,'url':url,'status':'failed','error':str(exc)}

if __name__ == '__main__':
    CACHE.mkdir(parents=True, exist_ok=True)
    results = list(ThreadPoolExecutor(max_workers=5).map(fetch, SOURCES.items()))
    ROOT.joinpath('evidence/source-retrieval.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(results, indent=2))

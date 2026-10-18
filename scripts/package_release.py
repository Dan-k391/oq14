"""Package a clean, tested source revision with PDF, proof logs, and Git history."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import zipfile
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'output'
parser = argparse.ArgumentParser()
parser.add_argument('--tag', required=True)
args = parser.parse_args()

def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=ROOT, text=True).strip()

commit = git('rev-parse', 'HEAD')
branch = git('branch', '--show-current')
assert not git('status', '--porcelain'), 'Source checkout must be clean.'
assert git('rev-parse', args.tag + '^{commit}') == commit, 'Tag must identify HEAD.'
build = json.loads((OUT / 'build-manifest.json').read_text())
checks = json.loads((OUT / 'verification.json').read_text())
lean = json.loads((OUT / 'lean/provenance.json').read_text())
assert build['source_commit'] == checks['source_commit'] == commit
assert not build['dirty_worktree'] and not checks['dirty_worktree']
assert lean['source_repository']['commit'] == commit
assert lean['source_repository']['dirty'] is False
assert all(c['passed'] for c in checks['checks'])
formal_sources = sorted([*(ROOT/'lean').glob('*.lean'),
                         *(ROOT/'lean/Maxwell').glob('**/*.lean'),
                         *(ROOT/'lean/HCurl').glob('**/*.lean'),
                         *(ROOT/'lean/HCurlDomain').glob('**/*.lean'),
                         *(ROOT/'lean/HCurlCutoff').glob('**/*.lean'),
                         *(ROOT/'lean/WeakPoynting').glob('**/*.lean')])
expected_theorems = set()
for source in formal_sources:
    expected_theorems.update(re.findall(r'#print axioms (OQ14(?:\.\w+)+)', source.read_text(encoding='utf-8')))
assert lean['compiler_exit_code'] == 0 and set(lean['checked_theorems']) == expected_theorems
pdf = OUT / 'pdf/oq14-manuscript.pdf'
assert hashlib.sha256(pdf.read_bytes()).hexdigest() == build['pdf_sha256']
assert hashlib.sha256((ROOT / 'lean/OQ14.lean').read_bytes()).hexdigest() == lean['source_sha256']
assert set(lean['source_hashes']) == {p.relative_to(ROOT/'lean').as_posix() for p in formal_sources}
for relative, digest in lean['source_hashes'].items():
    assert hashlib.sha256((ROOT/'lean'/relative).read_bytes()).hexdigest() == digest

source_zip = OUT / 'oq14-source.zip'
bundle = OUT / 'oq14-history.bundle'
git('archive', '--format=zip', '--output=' + str(source_zip), 'HEAD')
git('bundle', 'create', str(bundle), '--all')
verified = subprocess.run(['git', 'bundle', 'verify', str(bundle)], cwd=ROOT,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert verified.returncode == 0, verified.stdout
(OUT / 'bundle-verification.txt').write_text(verified.stdout, encoding='utf-8')
pages = len(PdfReader(pdf).pages)
release = f'''# OQ14 reviewed research release

Source branch: {branch}
Source commit: {commit}
Milestone tag: {args.tag}
Tracked and nonignored untracked working-tree changes: none.

The {pages}-page manuscript, {len(checks['checks'])} diagnostic groups, and {len(expected_theorems)} audited Lean theorem
declarations were rebuilt from this clean source revision. TeX references,
citations and overfull-box checks passed. Rendered layout was inspected.
Lean used 4.19.0 and the locked mathlib revision; all nine dependency
repositories were checked against the lockfile. The proof package was
rebuilt with an empty root build directory and retained pinned dependency
caches. Only propext, Classical.choice and Quot.sound occur in axiom reports.

The finite three-dimensional driven and genuinely normalized modal hotspot
theorems have complete written proofs under their stated conventions. The
modal theorem includes arbitrary high Q, fixed real pole frequency, common
ordinary material bounds and actual maxima in the prescribed plane patch.
The explicitly quantified unrestricted fixed-section channel assertion is
disproved for every fixed delta>eta>0, with the complete scattering map
selected as output. Stronger bypass or receiving-output versions remain
separate questions. The construction is an analytic proof, not a numerical
many-channel simulation. Lean checks the scoped declarations listed in its
README and build provenance, including actual weak local power conservation.
Full scattering, interface, channel construction and resonance proofs are
NOT yet formalized. Complete formal verification remains unfinished.

The source/ directory contains all tracked sources, build instructions,
proof reviews and research-stage evidence. Release artifacts and clean
build provenance are under artifacts/. The Git bundle preserves all
branches, tags and commits. Downloaded papers, compilers and dependency
caches are excluded. No repository was published.

Restore Git history with:
    git clone artifacts/oq14-history.bundle oq14
Then follow source/README.md and source/lean/README.md to reproduce builds.

Some source-tree research logs deliberately identify an earlier dirty
research run. The clean release records under artifacts/ are authoritative
for this milestone. Compilation and numerical diagnostics do not certify
the handwritten continuum proofs.
'''
(OUT / 'RELEASE.md').write_text(release, encoding='utf-8')
artifacts = [pdf, OUT/'build-manifest.json', OUT/'verification.json',
             OUT/'model-diagnostics.csv', OUT/'latex-final-pass.log',
             OUT/'compiler-output.txt', OUT/'lean/clean-build.txt',
             OUT/'lean/provenance.json', bundle, OUT/'bundle-verification.txt']
hashes = {str(p.relative_to(OUT)).replace('\\', '/'): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in [source_zip, *artifacts]}
(OUT / 'SHA256SUMS.json').write_text(json.dumps(hashes, indent=2)+'\n', encoding='utf-8')
delivery = OUT / 'oq14-delivery.zip'
with zipfile.ZipFile(delivery, 'w', compression=zipfile.ZIP_DEFLATED) as dest:
    with zipfile.ZipFile(source_zip) as src:
        for entry in src.infolist():
            dest.writestr('source/' + entry.filename, src.read(entry))
    dest.write(OUT/'RELEASE.md', 'RELEASE.md')
    dest.write(OUT/'SHA256SUMS.json', 'SHA256SUMS.json')
    for path in artifacts:
        dest.write(path, 'artifacts/' + str(path.relative_to(OUT)).replace('\\', '/'))
with zipfile.ZipFile(delivery) as archive:
    assert archive.testzip() is None
print(json.dumps({'source_commit': commit, 'tag': args.tag, 'pages': pages,
                  'delivery': str(delivery), 'bytes': delivery.stat().st_size,
                  'sha256': hashlib.sha256(delivery.read_bytes()).hexdigest()}, indent=2))

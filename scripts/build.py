"""Reproducible manuscript build, final-pass log checks, and provenance."""
from pathlib import Path
import argparse, hashlib, json, os, platform, re, shutil, subprocess, sys

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--tectonic',default=os.environ.get('TECTONIC'))
parser.add_argument('--cached',action='store_true',help='Disallow TeX package downloads')
args=parser.parse_args()
engine=args.tectonic or shutil.which('tectonic')
if not engine:
    local=ROOT/'.tools/tectonic/tectonic.exe'
    if local.exists(): engine=str(local)
if not engine: raise SystemExit('Install Tectonic 0.17.0 or set TECTONIC to its executable path.')
build=ROOT/'build'; build.mkdir(exist_ok=True)
out=ROOT/'output/pdf'; out.mkdir(parents=True,exist_ok=True)
cmd=[engine,'--untrusted','--keep-logs','--keep-intermediates','--outdir',str(build)]
if args.cached: cmd.append('--only-cached')
cmd.append(str(ROOT/'manuscript/main.tex'))
env=os.environ.copy()
env.setdefault('TECTONIC_CACHE_DIR',str(ROOT/'tmp/tectonic-cache'))
env['SOURCE_DATE_EPOCH']='1792281600'
proc=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
(build/'compiler-output.txt').write_text(proc.stdout,encoding='utf-8')
if proc.returncode: print(proc.stdout); raise SystemExit(proc.returncode)
log=(build/'main.log').read_text(encoding='utf-8',errors='replace')
bad=[line for line in log.splitlines() if re.search(r'(?:Reference|Citation).*undefined|There were undefined|multiply defined|Overfull \\[hv]box|^! ',line)]
if bad:
    print('\n'.join(bad)); raise SystemExit('Final TeX pass has unresolved references or layout errors.')
pdf=build/'main.pdf'
if not pdf.is_file(): raise SystemExit('Compiler returned without a PDF')
shutil.copyfile(pdf,out/'oq14-manuscript.pdf')
shutil.copyfile(build/'compiler-output.txt',ROOT/'output/compiler-output.txt')
shutil.copyfile(build/'main.log',ROOT/'output/latex-final-pass.log')
def git(*a): return subprocess.check_output(['git',*a],cwd=ROOT,text=True).strip()
manifest={'source_commit':git('rev-parse','HEAD'),'source_branch':git('branch','--show-current'),
          'dirty_worktree':bool(git('status','--porcelain')),
          'engine':subprocess.check_output([engine,'--version'],text=True).strip(),
          'python':platform.python_version(),'source_date_epoch':env['SOURCE_DATE_EPOCH'],
          'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),
          'final_pass_unresolved_references':False,'final_pass_overfull_boxes':False,
          'source_files':{str(p.relative_to(ROOT)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted((ROOT/'manuscript').rglob('*')) if p.is_file() and p.suffix in ('.tex','.bib')},
          'mathematical_verification':'Compilation does not verify the proofs.'}
(ROOT/'output/build-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in manifest.items() if k!='source_files'},indent=2))

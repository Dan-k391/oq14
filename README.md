# OQ14 research project

This is an auditable mathematical investigation of Miller and Monticone,
arXiv:2605.24738v1, Section 5.6. The original full channel conjecture is not
claimed solved. Every theorem is scoped in the manuscript and CLAIMS.md.
The user's subsequent request for complete closure and Lean verification
is tracked explicitly; proving an abstract operator implication does not
formally establish its physical Maxwell hypotheses.

The delivered results include a finite three-dimensional **driven** hotspot
packing theorem, with one finite-power illumination and explicit projection
constraints, and ten successfully compiled Lean theorems. The original modal
hotspot interpretation and unrestricted channel statement remain open.

Canonical mathematics: `manuscript/main.tex`, `manuscript/sections/*.tex`,
`manuscript/macros.tex`, and `manuscript/references.bib`.
Markdown files are indexes, reviews, and build instructions, not a second
mathematical manuscript.

## Build

Install Python 3.12 and Tectonic 0.17.0. Install the pinned Python dependencies:

```text
python -m pip install -r requirements.txt
python scripts/build.py
python scripts/verify.py
```

The one-command manuscript/diagnostic build is `make all`, with `PYTHON` set to the desired
Python executable if needed. On this Windows host the bundled Python is
`C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe`.
The portable engine is `.tools/tectonic/tectonic.exe`; alternatively set
`TECTONIC` or use `python scripts/build.py --tectonic PATH`.
Tectonic downloads standard TeX resources on first use; `--cached` prohibits
downloads after they have been cached. `TECTONIC_CACHE_DIR` can select a
shared cache. The default project cache is `tmp/tectonic-cache`.

For formal verification, follow `lean/README.md` to install the pinned Lean
dependencies, then run `python lean/build.py --log-dir output/lean` (or
`make formal`). This rebuilds the proof source and audits every theorem's axioms.

The official Windows compiler archive is
`tectonic-0.17.0-x86_64-pc-windows-msvc.zip` from the Tectonic GitHub release.
Its recorded SHA256 is
`f61ce51f0b0ade1015b7de7ef368541c5424e9756ecbd0d7af97d6d48030845f`.
The engine is not included in the source bundle. A conventional alternative
is `latexmk -pdf manuscript/main.tex`; the delivered PDF is tested with Tectonic.

## Outputs and evidence

- `output/pdf/oq14-manuscript.pdf`: compiled manuscript.
- `output/build-manifest.json`: exact source commit, clean/dirty flag, engine,
  source hashes, PDF hash, and final-pass checks.
- `output/verification.json` and `output/model-diagnostics.csv`: reproducible
  numerical diagnostics with source provenance.
- `output/latex-final-pass.log` and `output/compiler-output.txt`: compiler logs.
- `evidence/input-manifest.json`: presence and hashes of the supplied inputs.
- `evidence/source-retrieval.json`: public primary-source cache hashes and URLs.
- `evidence/diagnostic-reference.json`: an explicitly marked dirty-tree research
  run; the clean release run in output is authoritative for release provenance.
- `reviews/`: independent agent reviews, corrections, and remaining gaps.
- `lean/`: formal source and its explicit scope; consult its README and audit.
- `output/lean/`: clean release formal-build log and source/axiom provenance.
- `output/oq14-delivery.zip`: complete source, manuscript, clean evidence and Git history.
- `output/oq14-history.bundle`: all local branches, tags and commits.
- `output/RELEASE.md` and `output/SHA256SUMS.json`: exact milestone and file hashes.

The numerical program tests exact resonator models, corner monodromy, radial
Bragg identities and a local Maxwell flux Gram matrix. It does not simulate
a physical many-channel dielectric device. Missing physical bypass, port and
model-reduction certificates are recorded as null, not zero.

No successful TeX or Lean build is by itself a proof of a theorem that is
not represented in the formal source. No finite-dimensional formalization
is promoted to a verified continuum Maxwell result.

## Sources and version history

`python scripts/fetch_sources.py` optionally retrieves the public primary
papers into the ignored cache; `scripts/extract_inputs.py` audits the supplied
Downloads files on this host. Neither script is needed to build the manuscript.
Third-party full texts and downloaded toolchains are not redistributed.

The Git branches `hotspots`, `channel-bounds`, and `counterexamples` preserve
the reviewed tracks; `main` contains the integrated work. Agents used explicitly
nonoverlapping ownership recorded in OWNERSHIP.md. Milestone tags and the
release record identify reproducible checkpoints. A Git bundle is provided
for offline history; no remote publication is performed.

After the clean release checks and tag, `python scripts/package_release.py
--tag TAG` verifies matching clean provenance and creates the delivery archives.
Text sources use LF endings to keep their recorded hashes portable.

# OQ14

Maxwell channel and hotspot research, with a mathematical manuscript, Lean
formalizations, and preserved proof and review records.

**This repository does not claim full closure of the original OQ14.** The
checked results concern the explicitly quantified versions defined in this
project. Establishing that these versions settle the original question requires
additional mathematical justification.

## Start here

- [Current manuscript (PDF)](paper/oq14-manuscript.pdf) and
  [its build provenance](paper/README.md).
- [Canonical theorem statements](manuscript/sections/problem.tex),
  [scope index](PROBLEM.md), and [claim ledger](CLAIMS.md).
- [Lean endpoint entry point](lean/OQ14Closure.lean) and
  [verification guide](lean/README.md).
- [Frozen proof audit](checkpoints/2026-11-13-closure-release/AUDIT.txt)
  and [release record](checkpoints/2026-11-13-closure-release/release.json).
- [Repository map and archive conventions](docs/REPOSITORY.md).

## What the project establishes

| Result | Scope that matters |
|---|---|
| Channel counterexample | Fixed `delta > eta > 0`; the output is the complete outgoing scattering field, including reflection. Receiving-side transmission alone and stronger bypass requirements are separate questions. |
| Modal hotspot construction | Arbitrarily many finite hotspots in one outgoing mode under the project's reciprocal-residue QNM normalization, with a pole in a specified symmetry sector. Equivalence to the original intended mode-volume question is not established merely by the Lean proof. |
| Modal-volume family | Intrinsic phase traces, weighted maxima, and vanishing volume quantities for the same constructed family, under the definitions in the manuscript. Ambient rank-one modal simplicity is not asserted. |
| Driven hotspot construction | A finite three-dimensional dielectric and one fixed unit-power illumination; observation projections lie in the prescribed plane patch, but the maxima need not lie on that plane. |

The final recorded aggregate covers **2,171 project modules**, **10,946 inline
axiom reports**, and **23,697 kernel-safe declarations**. Reported dependencies
are limited to `propext`, `Classical.choice`, and `Quot.sound`. The audit retains
14 historical linter warnings and separately records unsafe executable
implementation declarations. Lean, mathlib, and package objects are trusted;
the compiler and all packages were not rebuilt from source.

These are the results recorded in the November 13 proof checkpoint. Uploading
the repository is not a new independent mathematical verification. A successful
Lean build proves the encoded statements, not their equivalence to a broader
research question. See [the audit](checkpoints/2026-11-13-closure-release/AUDIT.txt)
for the precise verification boundary.

## Build the manuscript

Use Python 3.12 and Tectonic 0.17.0:

```text
python -m pip install -r requirements.txt
python scripts/build.py
python scripts/verify.py
```

Set `TECTONIC` or pass `--tectonic PATH` if the executable is not on `PATH`.
The build also recognizes `.tools/tectonic/tectonic.exe` on Windows.
`--cached` disables TeX resource downloads after the first build.

Generated files go to `output/` and `build/`, which are ignored by Git. The
tracked `paper/` directory contains a deliberately saved manuscript snapshot;
it is not automatically overwritten by the build. The numerical verification
script runs model diagnostics, not a continuum Maxwell simulation or proof.

For Lean, use the [verification guide](lean/README.md). The historical
`make formal` / `lean/build.py` route covers an earlier set of registered
targets; it must not be described as reproducing the complete final aggregate.

## Project layout

| Path | Purpose |
|---|---|
| `manuscript/` | Canonical LaTeX mathematics, figures, and bibliography |
| `paper/` | Current saved PDF and its source/build provenance |
| `lean/` | Formal source, pinned toolchain, and dependency lockfile |
| `checkpoints/` | Frozen proof batches, audit manifests, and release evidence |
| `reviews/`, `handoffs/`, `checkpoint/` | Historical reviews and continuation records; read dates and scope |
| `evidence/`, `sources/` | Input/source records and research reading notes |
| `scripts/` | Manuscript build, diagnostics, and release utilities |
| `docs/` | Repository organization and upload conventions |

The November 13 frozen release is preserved at tag
`oq14-closure-2026-11-13`. Its 104-page PDF predates the newer explanatory
manuscript revision in `paper/`. Historical uses of “closure” or “complete”
refer to the project's stated targets, not full closure of original OQ14.

Downloaded papers, toolchains, dependency caches, compiled objects, unrelated
local projects, and unaccepted scratch work are not part of this upload.
Existing tracked audit logs and evidence archives are retained for provenance.

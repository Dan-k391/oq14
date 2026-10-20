# OQ14 continuation state — October 20, 2026

The user resumed the task. Work is active. The request is to finish the
written unrestricted-channel and modal-hotspot statements and their complete
Maxwell formalization in Lean. **The complete Lean task remains unfinished.**
Do not replace missing analytic proofs with hypotheses or custom axioms.

## Verified release and current sources

The latest coherent packaged release is `oq14-maxwell-foundations-1058`, commit
`29f7847b6a691080921859a4ca4d3586a038133e`. Its clean build passed all 1058
selected declarations in 83 modules, with only propext, Classical.choice and
Quot.sound; all 15 diagnostic groups passed; the 107-page PDF was inspected.
It is preserved in `output/checkpoints/oq14-maxwell-foundations-1058/` and
currently in the top-level delivery files.

- Delivery SHA256: `89aa39cabf0b707aa1873cb720f6dbcb9d9eefc36b1d7ecedc23bd9c61091bbf`
- PDF SHA256: `a66cdfdedf51d859535046a00bdaeda03fac78ec5bb946721e69129493d2ea45`

The latest packaged source has 1058 audited exports in 83 modules / 58 libraries.
The additional 240 exports passed targeted builds, independent source review,
the aggregate clean rebuild, manuscript rendering and packaging. Previous
818, 646 and 539 releases remain preserved in their checkpoint directories.
Newer active drafts are not included in that registered count. Consult the
release record before identifying the current source with a packaged PDF.

## New mathematical progress

| Module | Exports | Scope |
|---|---:|---|
| PointSingularity | 9 | Actual integration by parts across a point using Fubini |
| RealKernelBounds | 7 | All-radius real-frequency dynamic remainder bound and local L1 |
| KernelGradient | 6 | Actual outgoing gradient bounds and first weak derivative |
| KernelSource | 13 | Weak dynamic Hessian and exact outgoing scalar Dirac source |
| DynamicSource | 7 | Actual full dyadic decomposition and Maxwell Dirac source |
| NewtonConvolution | 11 | Spatial weak Newton convolution and Fourier identity |
| NewtonL2 | 21 | Actual spatial response equals -P; unique bounded L2 extension |
| NewtonL1L2 | 11 | Ordinary/Plancherel agreement and spatial response for L1∩L2 |
| StaticNewton | 9 | Actual compact-material static block; inverse bound one |
| ModalOrigin | 44 | Entire dipole center extension and actual Maxwell equations there |
| WeakPoynting/DivCurl | 6 | Actual Schwartz div-curl energy identity |
| WeakPoynting/DivCurlCompact | 7 | Actual compact graph approximation |
| WeakPoynting/DivCurlRegularity | 8 | Nine actual weak L2 derivatives and energy identity |
| WeakPoynting/LocalRegularity | 9 | Local magnetic H1 from regional weak Maxwell equations |
| WeakPoynting/RegularityBounds | 4 | Quantitative cutoff H1 bound with bounded permittivity |

Precise hypotheses and limits are in `lean/README.md`, the verification
section of the manuscript, and `reviews/`. KernelSource and DynamicSource
retain the full singular Newton contact term. ModalOrigin does not itself
assemble the spherical weak interface or identify the full resolvent pole.
Local H1 does not itself prove compact embedding or general field traces.

## Active continuation tracks

The frozen registered source now has 1312 audited exports in 110 modules /
82 libraries. Its next clean aggregate build and package are pending.
The coherent 1058 package listed above remains the latest release.

The root owns registration, shared ledgers, clean builds and release packaging.
Agents share the same directory; never delete their root build artifacts.

- Root: actual scalar and dyadic radiation, Silver--Müller at the spatial
  infinity filter, and the assembled outgoing small-volume existence theorem
  are frozen and independently reviewed. Regional H(curl) and physical power
  conservation are also proved for the actual fields.
- Channels: actual continuous exterior representatives, L2-kernel convolution
  compactness and arbitrary-support weighted dynamic compactness are frozen.
  The next work is actual static-inverse preconditioning and a proved generic
  compact-operator Fredholm argument; the pinned library lacks the alternative.
- Hotspots: actual nonzero shell L2 residue, Banach analyticity and standard
  meromorphic order minus one are frozen. ModalPoleMode and ModalOutgoing
  are subsequent drafts tying the same residue to global modal fields and
  an explicit complex-frequency radiation condition.
- Counterexamples: interior compact-C1 test density, weak-curl upgrade,
  material Caccioppoli and actual scalar exterior C2 Helmholtz regularity
  are frozen. The next work constructs actual exterior C∞ fields by a local
  smooth kernel cutoff, then classical Maxwell equations.

New drafts are outside the registered count. Inspect source, reviews and
compiler results before treating them as proved. Avoid aggregate builds
over active drafts; use the committed clean checkout below.

Further work includes arbitrary-size outgoing solvability and uniqueness,
all-angular-order Green convergence and whole-plane flux, conical coefficients
and Runge, rounding, analytic Fredholm theory, reciprocal normalization and
infinite-degree modal isolation. The full channel and hotspot constructions
are not Lean theorems yet. Continue the task, not just checkpoint maintenance.

## Scientific scope

The written unrestricted fixed-section channel finiteness assertion is
disproved for each fixed delta>eta>0 with the complete scattering map selected
as output, common ordinary positive material bounds and frequency, and
unrestricted finite support. Stronger bypass thresholds, receiving outputs,
and uniformly bounded support are separate questions.

The written modal hotspot theorem constructs one genuinely normalized high-Q
mode with arbitrary finite peak count, fixed real frequency, common ordinary
bounds, and actual maxima in the prescribed plane patch. Contrast may depend
on N within those bounds. Do not broaden or silently change these quantifiers.

## Reproduction and clean-checkout workflow

Workspace `D:/oq14`; PowerShell. Pinned tools:

- Python: `C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`
- Lake: `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`
- Tectonic: `D:/oq14/.tools/tectonic/tectonic.exe`
- Lean4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; nine locked dependencies.

Use `tmp/clean-checkout` for aggregate verification; its dependency junction
reuses the pinned root packages while its root build directory is independent.
After committing only the frozen batch, fetch this local repository there and
check out that exact commit. Run its `lean/build.py --lake <path> --log-dir
output/lean`, `scripts/verify.py`, and `scripts/build.py --cached --tectonic
<path>`. Set `TECTONIC_CACHE_DIR=D:/oq14/tmp/tectonic-cache`. Inspect the changed
PDF pages before packaging with `scripts/package_release.py --tag <tag>`.
Copy only coherent verified artifacts back into a new output checkpoint.

Targeted development from `lean/`: `lake env lean File.lean`; add
`-o .lake/build/lib/lean/File.olean` when an importable artifact is needed.
No dependency upgrade is authorized by routine proof development.

The October18 historical drafts and their verified manifest remain under
`checkpoints/2026-10-18-resume/`; its source tag and portable checkpoint archive
are preserved. Their old error lists are historical, superseded by this work.
No repository was published. Continue the active mathematical task rather than
mistaking this status file or a source milestone for completion.

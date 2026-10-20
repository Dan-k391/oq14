# OQ14 continuation state — October 20, 2026

The user resumed the task. Work is active. The request is to finish the
written unrestricted-channel and modal-hotspot statements and their complete
Maxwell formalization in Lean. **The complete Lean task remains unfinished.**
Do not replace missing analytic proofs with hypotheses or custom axioms.

## Verified release and current sources

The latest coherent packaged release is `oq14-maxwell-foundations-1660`, commit
`f7e03a7db06c084abb1279e0affef93d3a72082c`. Its clean build passed all 1660
selected declarations in 134 modules / 106 libraries, with only propext,
Classical.choice and Quot.sound. All 15 diagnostic groups passed. The 108-page
PDF has no unresolved references or overfull boxes; the front matter and
changed verification/verdict pages were visually inspected.

Fourteen matching artifacts were copied with hash verification to
`output/checkpoints/oq14-maxwell-foundations-1660/` and the top-level output.

- Delivery SHA256: `31190f182f399636e9f1bcbbcf6522ec4dba05191924cb685bf48dc8bb41b777`
- PDF SHA256: `2292c6663c7da4813c4321154d078c7bd258d71f7c408cb684bee63db43f0543`

Previous 1312, 1058, 818, 646 and 539 releases remain preserved. Newer active
proofs are not included in the registered count. Consult the release record
before identifying current working sources with a packaged PDF.

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

The coherent 1660 release passed the clean rebuild, diagnostics, PDF build,
visual checks and packaging at one exact source commit. Work continues on
the newer proofs listed below; these are outside the 1660 package.

The 1835-declaration clean aggregate passed at commit
`44ca66d9d6db10e555ae1881bdc1399aefb88100`, with clean provenance and all
15 diagnostic groups passing. Its PDF failed on two line overflows.
That layout is corrected in the next batch; 1835 was not packaged.

The next frozen registered source has **2033 exports in 176 modules /
148 libraries**. All 24 new modules passed targeted compilation and
full-source audit. The key completed bridges are actual exterior scalar
and Maxwell Rellich, actual spherical harmonic density and moment
equations, complex volume reciprocity, and finite-rank Laurent principal
coefficients. Its clean combined verification and package remain pending.

The root/Astra owns central proof design, mathematical audits, registration,
shared ledgers and release packaging. The user explicitly requested
6.1 Sol subagents. Agents share the directory; never clean the root
Lean build artifacts while they are active. Use the independent committed
clean checkout for aggregate checks.

Active work after 2033:

- Root: constant-coefficient continuation using actual harmonic moment
  equations on finite radial intervals; integration and release.
- reciprocity_sol: `AnnularMoment.lean`, genuine differentiation and
  second continuity for fields smooth only on a finite annulus.
- modal_sol: `RadialIntervalUniqueness.lean`, actual finite-interval radial
  uniqueness from zero Cauchy data and the genuine Hankel Wronskian.
- fredholm_sol: `LocalHelmholtzRepresentation.lean`, actual compact smooth
  Helmholtz Green representation from the proved kernel Dirac identity.

The main continuation design is to propagate zero from a center
neighborhood to an interior ball using the proved harmonic moments and
finite-interval ODE uniqueness. This avoids assuming PDE analyticity.
Kernel spatial analyticity alone does not prove solution analyticity;
pinned mathlib has no general elliptic regularity or analytic integral
API. Weak-to-smooth regularity and material-interface continuation still
need genuine proofs.

Further work includes global arbitrary-support homogeneous uniqueness
and outgoing solvability, all-angular-order Green convergence and
whole-plane flux, conical coefficients, Runge, rounding, physical
reciprocal normalization and infinite-degree modal isolation. The full
channel and hotspot constructions are not Lean theorems yet.
Continue the task, not just checkpoint maintenance.

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

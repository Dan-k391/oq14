# OQ14 continuation state — October 20, 2026

The user resumed the task. Work is active. The request is to finish the
written unrestricted-channel and modal-hotspot statements and their complete
Maxwell formalization in Lean. **The complete Lean task remains unfinished.**
Do not replace missing analytic proofs with hypotheses or custom axioms.

## Verified release and current sources

The latest coherent packaged release is `oq14-maxwell-foundations-1312`, commit
`ed0d41181a0e9c3ebef586e04cc7c590d15bab91`. Its clean build passed all 1312
selected declarations in 110 modules, with only propext, Classical.choice and
Quot.sound; all 15 diagnostic groups passed; the 107-page PDF was inspected.
It is preserved in `output/checkpoints/oq14-maxwell-foundations-1312/` and
currently in the top-level delivery files.

- Delivery SHA256: `089ef47e3953013368c53cb81069aeafb8c4de9547a8394d3d2490d5e6c0a43f`
- PDF SHA256: `7abf20801ae4fb1c6d24012ac8924cb245a21a420082c9b7cae3856434df72cd`

The latest packaged source has 1312 audited exports in 110 modules / 82 libraries.
The additional 254 exports passed targeted builds, independent source review,
the aggregate clean rebuild, manuscript rendering and packaging. Previous
1058, 818, 646 and 539 releases remain preserved in their checkpoint directories.
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

The coherent 1312 release passed its clean build, diagnostics and package at
one exact commit. Fourteen coherent artifacts were copied with hash verification
to the immutable checkpoint and top-level output directory.

The next frozen registered source now has 1660 exports in 134 modules /
106 libraries. All 24 new modules passed targeted compilation and independent
source audit; the new clean aggregate build and PDF package are pending.
The top-level output still correctly identifies the coherent 1312 package.

The root owns registration, shared ledgers, clean builds and release packaging.
Agents share the same directory; never delete their root build artifacts.

- Root/Astra: ScalarFarField8, MaxwellFarField15 and FarFieldPower9 compiled
  and passed independent source review. The actual electric/magnetic amplitudes,
  transversality and radial outgoing power limit are established. AngularPower
  compiled and passed independent review, deriving the genuine spherical
  integral from a uniform bound. Root now owns PolarIntegration and the
  weak-power-to-zero-total-flux bridge.
- fredholm_sol (6.1 Sol): CompactPerturbation6, CompactAlternative7,
  VolumeFredholm7 and VolumeAlternative8 compiled and were audited. The last
  is explicitly conditional on homogeneous volume uniqueness. ComplexGreenKernel15
  and ComplexDynamicKernel14 also compiled and were audited. L2Parametric2,
  ComplexKernelAnalytic18 and ComplexConvolutionAnalytic37 now prove genuine
  Banach holomorphy, actual complex compactness and an invertible zero value.
  HilbertFiniteRank and analytic Fredholm reduction are active.
- modal_sol (6.1 Sol): ModalPoleMode9, ModalOutgoing22, ModalPoleRadiation7
  and ModalScaling24 compiled and passed root review. These concern actual
  nonzero global weak fields, complex-frequency outgoing limits and prescribed
  real frequency. ModalScaledPole30 compiled and passed root review, including
  the physical shell measure and exact frequency-rescaling residue factor.
  ModalMatchingNorm16 is a newer audited draft outside 1660; it proves the
  actual finite matching derivative pairing, not the physical volume norm.
  The agent now owns FiniteRankSchur for the Fredholm reduction.
- reciprocity_sol (6.1 Sol): KernelReciprocity29 and NewtonReciprocity16
  compiled with permitted dependencies and passed root review. The actual
  untruncated compact-source electric response is bilinearly reciprocal.
  L1KernelOperator18 compiled and passed root review, constructing bounded
  linear dependence of the actual L2 convolution operator on its L1 kernel.
  SphereMeasure3 proves actual angular open-set positivity. AngularPowerZero6
  is a newer audited draft outside 1660. RadialPowerTest is active.
- ExteriorSmooth9 and ExteriorClassical18 compiled and passed root review:
  actual compact-L1-source exterior fields are smooth and obey classical
  Maxwell and Gauss equations.

The user explicitly requested 6.1 Sol subagents and Astra for the important
parts. Root retains mathematical audits and shared integration. Former agents
channels, counterexamples and hotspots hit their usage limits; their completed
source was reviewed before reassignment. Do not resume their errored runs.

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

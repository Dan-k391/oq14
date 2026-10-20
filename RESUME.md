# OQ14 continuation state — October 20, 2026

The user resumed the task. Work is active. The request is to finish the
written unrestricted-channel and modal-hotspot statements and their complete
Maxwell formalization in Lean. **The complete Lean task remains unfinished.**
Do not replace missing analytic proofs with hypotheses or custom axioms.

## Verified release and current sources

The latest coherent packaged release is `oq14-maxwell-foundations-818`, commit
`618be804c984614f49efb1d109e9a08ed39ada6e`. Its clean build passed all 818
selected declarations in 60 modules, with only propext, Classical.choice and
Quot.sound; all 15 diagnostic groups passed; the 106-page PDF was inspected.
It is preserved in `output/checkpoints/oq14-maxwell-foundations-818/` and
currently in the top-level delivery files.

- Delivery SHA256: `0b15ed1c506781a11d158679aebbb5f8fae51df9b8ba46663132ac0e9b9f9712`
- PDF SHA256: `cda469595ed0939ea552fd9b06d0198a6da352b3cd2fbf3665802eaffe995e9a`

The latest packaged source has 818 audited exports in 60 modules / 41 libraries.
The additional 172 exports passed targeted builds, independent source review,
the aggregate clean rebuild, manuscript rendering and packaging. Previous
646 and 539 releases remain preserved in their checkpoint directories.
The next registered source batch has 1058 audited exports in 83 modules /
58 libraries. Its aggregate clean build and package are separate steps.
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

The root owns registration, shared ledgers, clean builds and release packaging.
Agents share the same directory; never delete their root build artifacts.

- root: the 1058 batch includes NewtonWeak5, KernelConvolution6,
  WaveResponse3, FieldResponse5, MagneticResponse10 and MaterialMaxwell7.
  Both actual first-order source equations and their material substitution
  are proved on compact smooth tests. Active ScalarRadiation and
  SmallVolumeMaxwell drafts extend this to radiation bounds and explicit
  locally L2 field existence; inspect their compiler status before using.
- channels: the 1058 batch includes L1Convolution16, DynamicConvolution13,
  DynamicVolume14, Constants2, LocalVolumeResponse7, MaterialField7 and
  IncidentLocalization5. Actual source, inverse, local electric L2 and
  polarization self-consistency are proved. Subsequent LocalConvolution5
  and MagneticLocal3 supply magnetic local L2; inspect freeze status.
- hotspots: the 1058 batch includes SphereRemovable11, RadialInterface23,
  ModalProfiles34 and ModalWeak21. Genuine global weak high-Q spherical
  fields include the electric normal jump and exact outgoing Hankel exterior.
  ModalLocal and subsequent H(curl) assembly are active separate modules.
- counterexamples: the 1058 batch includes PartialSmoothing9, Translations7,
  Compactness10, MagneticCompactness6, ElectricControl8 and
  MaxwellCompactness11. Both E and H are locally precompact for one fixed
  positive bounded coefficient. InteriorTestDensity and RegionalCurlUpgrade
  subsequently extend compact smooth identities to the actual regional
  compact-C1 weak-curl definition; inspect freeze status.

These newer files may be unregistered or unfinished. Inspect their current
source, reviews and compiler logs before using them as proved results.
All compiler sessions from a previous turn must be checked rather than assumed
complete. Avoid running the aggregate build over active drafts.

Further work still includes global outgoing scattering, actual dynamic
volume solvability/radiation, all-angular-order Green convergence and whole-plane
flux, conical coefficients and Runge, rounding, analytic Fredholm theory,
reciprocal normalization and infinite-degree modal isolation. The full channel
and hotspot constructions are not Lean theorems yet.

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

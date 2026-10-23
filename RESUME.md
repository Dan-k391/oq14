# Active OQ14 continuation — October 23, 2026

**ACTIVE. Full OQ14 closure and complete Maxwell Lean formalization remain unfinished.**
The user resumed work on October 23. Continue with 6.1 Sol subagents and
retain the root for critical mathematics and integration. No stop request
is pending. Do not turn targeted results into a claim of full closure.

## Immutable recovery and clean release

October 22 checkpoint: `checkpoints/2026-10-22-resume/`, tag
`oq14-resume-2026-10-22`, HEAD at start
`d16d698861ec48e4d52ac9a982af94c788d09681`. All142 working and286 evidence
files were hash-verified before this continuation. The immutable checkpoint
contains the older RESUME and exact agent handoffs. Its missing-only restore
script does not overwrite current work. Archive:
`output/oq14-resume-checkpoint-2026-10-22.zip`, SHA256
`a93ee83f0d11bd2c6a85c849b2c0fd84706f809eb08d6abc7e2091225456d202`.

Latest clean combined release remains `oq14-maxwell-foundations-4391` at
`c597c535c9a751fccbf3e9a0d644721326ceda26`: 4391 audited reports /469 modules /
441 libraries, clean aggregate exit0, nine pinned dependencies, all15
diagnostic groups passed. Matching113-page PDF SHA256
`8c29cdc3b31ee277cdb7e0b9efc3a54669eb69b85e46d38af052a0b060ad22ce`.
Matching delivery ZIP9365092bytes SHA256
`89f16629977b6477345ca0732357fc0bf468ee32def7d0570fec75ec4eafe0c3`.
All14 artifacts are under `output/checkpoints/oq14-maxwell-foundations-4391/`
and top-level output. See `reviews/clean_release_4391.md`.
Clean clone `tmp/clean-checkout` remains at this release. Older releases and
checkpoints remain preserved. The October 23 registration is now 5238
reports /627 modules /599 libraries: 847 new reports in158 modules.
Exact frozen sources and independent receipts are tracked in
`reviews/audited_constructions_5238.json`; registration scope is in
`reviews/actual_constructions_5238.md`. Matching clean aggregate is next,
in a fresh isolated checkout, never the root agent workspace. No new
aggregate release, paper rebuild or external publication has completed.
`tmp/integrate_current_audits.py 5238` has run; do NOT rerun it.

## Current source and evidence

`tmp/audited_after_4391.json` is the authoritative incremental independent
source/log hash manifest. At this update it records158 modules /847 selected
reports, beyond the clean release. More author-final modules and drafts
are in progress; inspect their reviews and latest logs before use.
These targeted checks are NOT a new combined clean build.

All ten previously pending audits and the formerly uncompiled
ConicalRoundedHCurl draft now independently pass. Every recorded report
uses only propext, Classical.choice and Quot.sound. No source placeholders
or new project axioms are permitted. Compiler error-recovery reports are
not verified proofs. Root alone registers modules and edits release ledgers.

`tmp/record_after_4391.py` checks root audit receipts;
`tmp/record_modal_after_4391.py` checks modal independent reviews, including
acronym-aware filenames. Both reject changed frozen records. Never rerun
old one-time integration/preservation/checkpoint scripts blindly.

## Root: actual Maxwell modes and vector reaction

SourceRadiationFrequency6 now proves frequency-scaled outgoing radiation
for actual all-layer TM/TE weak Maxwell fields. Tests still avoid the
origin: this is not the full point-source distribution normalization.
SolidMaxwellProfiles8 identifies globally smooth regular E/H with their
literal radial profiles. SourceCoreReaction7 identifies actual layered
minus vacuum source fields in the core with (gamma+I) times regular fields.
The physical scalar/tensor reaction coefficient has the separate negative
sign -(gamma+I); do not confuse these conventions.

ScalarPlaneWaveMoment7, ToroidalPlaneWaveMoment6 and
PoloidalPlaneWaveMoment9 independently pass. The scalar constant/phase is
derived from the actual Green source jump. The toroidal moment is
4*pi*I^l*k^l times the solid toroidal field. Taking its actual curl gives
the poloidal moment 4*pi*I^l*k^l/(I*k) times the solid TM electric field
for every nonzero real k, including all spatial origins; a division-free
identity also covers k=0. Both are literal sphere integrals.

DebyeJetBounds7, VectorReactionTerms7, VectorReactionSeries3 and
VectorReactionLimit7 independently pass. They prove genuine bounds,
differentiation and compact uniform jet convergence of the literal
normalized vector reaction series. SolidWaveParity6 independently proves
actual TE/TM central-inversion parity. RadialVectorParity4,
CentralReactionExpansion5, VectorLimitIdentification6, VectorLimitJets7 and
PairedVectorKernelLimit3 independently pass. The literal paired vector
series converges with every fixed finite derivative order to the actual
central-inversion J gain kernel on compact regions including origins and
coincident points. HalfTurnMaxwellParity11 independently passes:
genuine proper-rotation covariance yields
the plane-wall bridge only for invariant fields. Full outgoing spatial
dyadic/point-source identification remains required.

## modal_sol: actual transverse expansion and vector kernel

The degree-zero polynomial case, homogeneous restriction injectivity,
actual vector polynomial span, continuous/L2 density, constructed
representative basis span and normalized transverse separation all pass.
TransverseHarmonicBasis10 constructs a genuine normalized real transverse
Hilbert basis. ComplexVectorSphere9 and ComplexTransverseExpansion4 give
actual complex real/imaginary bridges and HasSum/inner-product expansion
for every AE-tangential complex vector L2 field, without a completeness premise.

TransversePlaneFields8 independently passes: actual projected plane fields
have inner product equal to the literal sphere reaction integral; its
rank-one expansion equals J(k,x-y) with k^3/(16*pi^2).
PlaneFieldCoefficients6, PlaneDebyeCoefficients4, DebyeReactionExpansion2,
SolidWaveReality7 and DebyeUnitReaction6 independently pass. The actual
J kernel now has a genuine HasSum expansion in the normalized regular
Maxwell dyads, with no completeness or coefficient premise.
SourceFarAmplitude7, PointDyadicFarField2 and FreeSourceCoefficients10
independently pass: actual outgoing ray amplitudes and exact far-field
source coefficients, with no normalization premise. HankelExteriorBounds9
and AngularExteriorBounds7 independently pass uniform exterior estimates
and exact factorial cancellation. VacuumOutgoingBounds and OutgoingDyadBounds
are downstream. The full outgoing series/Rellich and source-response
identification remain.
Central inversion and plane reflection must not be identified for the full
tensor; the latter needs the specified C2-invariant illumination sector.

Existing scalar Green expansion is literal and pointwise for nonzero
x,y with unequal radii. Existing physical scalar reaction jet bounds and
limits include origins, but the radius must be large enough for the chosen
finite derivative order: R>=exp(1)*B and B>=degreeScale(order,ball).
Do not claim all derivative orders at one insufficient fixed radius.

## fredholm_sol: actual finite illumination Runge and rounded peaks

ConicalRoundedHCurl10 and ConicalRoundedHotspot3 now independently pass:
actual material weak Maxwell pairs and genuine Hcurl rounded families
have positive-volume superlevel sets above every prescribed threshold.
The explicit tip gate is zero at radius<=1/(n+1), one at>=2/(n+1), preserves
common contrast/outer support and converges AE. No plane maxima are implied.

ConicalSeparatedSource12 truncates material to a closed ball a<cutoff.rIn,
preserves the exact singular static field, and derives a physical source
zero on the entire material ball. ConicalRungeAnnihilator7 derives actual
plane-wave annihilation -> radiation zero -> exterior Rellich -> reciprocal
pair zero. ConicalRungeBall8 and ConicalRungeClosure5 prove actual restricted
ball Hilbert density using the conjugated compact source extension, then
literal finite transverse plane-wave approximation of the separated target.
ConicalPlaneWaves9 and ConicalFinitePlanes6 derive both entire Maxwell
fields and their exact restricted L2 representatives.

ConicalBallExtension8, ConicalBallRestriction6 and ConicalMaterialRunge5
independently pass the actual bounded extension/restriction and material
inverse transfer. ConicalSeparatedDynamic9, ConicalSeparatedMaxwell12 and
ConicalSeparatedPotential9 independently pass: identical static-field limit,
actual local Maxwell laws, genuine weak potential and uniform quadratic
correction bound. The actual gradient graph, angular moments, radial
energy, Gauss equation, classical system and finite-energy expansion now
independently pass. ConicalSeparatedPairing5, Identity2, Limit3 and
Retention3 independently derive a nonzero singular coefficient at every
sufficiently small positive frequency. ConicalSeparatedHotspot4 is
author-final and awaiting independent audit. ConicalIllumination and the
final rounded finite-illumination realization are under development.
The older annular coefficient retention is not automatically the new
separated-data theorem. L2 peaks alone do not give fixed-point or 3D maxima.

## continuation_review_sol: channel flux and restricted TE inputs

Actual density differentiation, both weak vacuum curl equations, modified
incident datum and the full material weak Maxwell pair now independently
pass. FiniteBallWeak2 derives inverse smallness from shrinking support.
FiniteBallPlaneFields2 constructs a genuine continuous strip representative
and its actual plane flux. Never restrict a bare 3D AE equality to a plane.

StaticSourceTail2, StaticCoherentRemainder6 and FiniteStaticCoherent3
independently pass: whole-plane dynamic-minus-static coherent flux is
bounded by source mass times finite illumination coefficient mass, uniformly
in the positive moving gap. StaticTrialLimit2 removes the actual quadratic
self-flux too. FiniteSphereDipoleFlux2 identifies literal static polarized
balls with exact volume-weighted dipoles. FiniteSphereDipoleLimit1 independently
passes: complete actual inverse totalFlux converges to
that dipoleFlux in whole-plane L1, with source mass/error/gap derived.

IMPORTANT remaining input scope: current finite J/K point columns are
larger than the manuscript's even-l/even-m TE band. Do not identify them
with that restricted sector. Agent is now prioritizing literal ct:jets
scalar Herglotz/Debye TE construction, equatorial and half-turn symmetry,
actual finite-band interpolation and incoming power, before Gram balancing.
SymmetricScalarWaves11 and DebyePlanarJets3 independently pass actual
Helmholtz/Maxwell fields, both symmetries and the needed edge trace formulas.
EntireExponentialPackets4, EntireRealIdentity2 and BivariateExponentialPackets2
independently prove literal finite polynomial-exponential independence on a
real rectangle. EdgeCosineJets3 and EdgeScalarInterpolation3 now prove
the actual scalar edge-jet spanning theorem. SymmetricScalarJets3,
ScalarFiniteCalculus4, HarmonicHalfTurn6 and AngularScalarJets4 independently
pass. EvenHarmonicProjection7 is author-final; angular symmetry and actual
finite restricted harmonic interpolation are next. Physical input power,
Gram balancing and finite-stack/channel identification remain.

## Final scope and safe continuation

Still essential: full spatial dyadic/source normalization; finite-stack
identification; restricted finite input jets and physical Gram/power;
final rounded driven realization; actual reciprocal modal residue
normalization; infinite-degree pole isolation; simultaneous 3D modal maxima
in the prescribed plane patch. Written channel scope is delta>eta>0,
complete scattering output, fixed frequency/common material bounds and
unrestricted finite support. Other parameter/output/support variants are
separate. Written modal scope uses actual reciprocal-residue normalization,
arbitrarily high Q, fixed real frequency, common bounds and N-dependent
insertion contrast. No full-closure claim yet.

Original Downloads manual was absent at the last recorded comparison;
see `reviews/original_scope_2026_10_20.md`. No current exact comparison claimed.

Workspace D:/oq14, PowerShell. Python:
C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe
Lake: D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe.
Lean4.19.0/mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, nine pins.
Compile in cwd lean, never root. Do not rebuild a dependency while checking
its dependent module. Never clean root lean/.lake/build. Some logs use
UTF16 BOM; decode accordingly. Use explicit UTF8 for Python file reads.
Only record a module after complete source review and clean fresh compiler.
Unrelated sites/ must not be touched, staged or packaged.

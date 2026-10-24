# OQ14 resume state — October 24, 2026 (third continuation, in progress)

Full OQ14 closure and complete Maxwell Lean formalization are still unfinished.
Work resumed on October 24 from the paused checkpoint `oq14-resume-2026-10-23`
(commit `3d5329e`). This file supersedes the October 23 stop note; the dated
checkpoint folder `checkpoints/2026-10-24-continuation/` carries the stage log,
ledger copies and compiler evidence for everything added today.

## Exact verification boundary (unchanged release)

The last clean combined release remains `oq14-maxwell-foundations-5238`,
commit `8a4a8bf4abb15d7ae6f2fc0fa4d63758c3c04248`: 5238 proof reports,
627 modules, 599 libraries, nine pinned dependencies, all 15 diagnostic groups
passed, 113-page PDF (SHA256 `611c64b2…b649d1`, delivery ZIP
`ba907a88…4db1c7`). No clean aggregate release, publication or registry change
was made today. Release 5238 is immutable.

Beyond that release, the incremental ledger `tmp/audited_after_5238.json`
(copied into the checkpoint folder) records independently reviewed and freshly
compiled modules: 270 modules / 2235 reports at the latest third-continuation
commit `d20add2` (226 / 1334 at the end of the second continuation, 169 / 832 at
the October 23 stop).
Every recorded report uses only `propext`, `Classical.choice` and `Quot.sound`
(some pure-algebra reports use `propext` alone). "Independently audited" means a
complete-source mathematical review by someone other than the author plus a
fresh pinned compile from source without the author's object, exit 0, no
warnings, with the receipt `reviews/<module>_independent.md` carrying exact
source and log hashes. Root audits subagent work; the modal subagent audits root
work. Author-only status is always stated as such. These targeted checks are
NOT a new release. The ledger's source and log hashes were verified against the
files on disk before the final commit.

## What was done on October 24 (independently audited unless marked)

Resume stage 1: the seven modules left author-only at the stop were audited
(CompactCoreKernel 7, SourcePairedCore 5, ConicalUniformBall 3,
FiniteAngularNonzero 4, SphereVectorPairing 5, FiniteMixedFields 13,
RestrictedTEFieldLinear 4).

Modal/hotspot branch (modal Sol author, root audit): FiniteMixedTraces 13
(repaired; finite incoming trace bridge), FiniteMixedFlux 3, FiniteMixedInwardFlux 3
(inward Poynting integral of the incoming half-fields tends to 2 pi^2 times the
amplitude energy, positive for nonzero coefficients), FiniteMixedHerglotz 11
(EXACT identity: `FiniteAngularHerglotz.incident k c` is the finite mixed
regular Debye field at k times the point), FiniteMixedScaledFlux 14 (1/k^2
scaling derived; `normalizeK k c` has unit limiting inward half-field power),
SimplePoleResidueForm 2, AxisymmetricPlaneMaximizer 7 (geometry),
LosslessSphereFluxConstancy 10 (for the global weak Maxwell class the sphere
flux vanishes for almost every radius). Scope note:
`reviews/modal_closure_scope_2026_10_24.md`: the smallest missing modal theorems
are `weighted_mode_in_volume_kernel` (needs a complex-frequency radiation
representation), Hermite–Lindemann (absent from Mathlib), and the modal
continuation/rounding assembly. Do not claim modal closure.

Fixed-angular branch (fredholm Sol author, root audit): ConicalFixedAngularInput 3,
ConicalFixedInputTransfer 8 (fixed input chosen per small positive frequency
BEFORE rounding level, radius, coordinate and threshold; eventually
positive-measure superlevel sets of the rounded total field at every threshold),
ConicalNormalizedInputTransfer 6 (same with the unit-limiting-inward-power
normalization), ConicalNormalizedInputHCurl 2, ConicalNormalizedInputCoefficient 5
(nonzero singular coefficient and projected-graph identity for the normalized
input, by uniqueness under scaling; the gauge system is affine in the incident).
The input depends on k; "normalized" means the limit of the inward half-field
Poynting integral equals one, not finite-radius or total-field power; no
plane-maximum claim.

Channel branch (channel Sol author, root audit): RestrictedTEDatumLinear 4,
MaterialSourceLinear 2, RestrictedTEPolarization 4, RestrictedTETotalLinear 44
(`uniform_actual_inverse_to_dipoles`: whole-plane L1 error uniform over the
sup-norm polydisc of a fixed finite index set), RestrictedTEUnitSphere 4
(uniform over the physical-power unit ball of the span of an orthonormal family),
RestrictedTEPassageTransfer 5 (passage/bypass defined; transfer of thresholds
under uniform L1 error, all thresholds explicit), RestrictedTEParitySandwich 8
(`ParityMaterialField.block d k B = 1 - S c * parityKernel * S c`, so the parity
device is the named shell block of the shell-inclusion algebra, and shell plus
disjoint inclusion is the named combined block). Scope note:
`reviews/channel_closure_scope_2026_10_24.md`; findings: no m-labelled
harmonic basis exists in the tree (the even sector is intrinsic), `Index` is a
free space on polynomials rather than a basis, and the interpolation geometry is
narrower than the manuscript's. Remaining: dipole-flux concentration and plane
jets, unit throughput / `ca:powerbudget` (needs a Riemann–Lebesgue cross-term
step), the physical finite-stack Green identification.

Root (Astra) source/inclusion branch (modal Sol audits unless marked):
SourcePairedInverse 8, SourceCoreOperator 8, ShellInclusionAlgebra 18,
ShellInclusionBlocks 3, ShellInclusionVolume 12 (the dynamic volume block IS
`1 - S c * kernel k R * S c` with the coefficient-independent kernel
`DynamicConvolution.operator k (2R) - physicalProjection`; coefficient sum with
disjoint supports; exact combined-block reduction with explicit inverse),
ShellInclusionReaction 3 (effective block = inclusion block minus the reaction
operator `Si T Ss r Ss T Si`), ShellInclusionSmall 8 (smallness makes the
effective block a unit), ShellInclusionTruncation 3 (the volume block is
independent of the enclosing radius once it contains the support). Fredholm Sol
author, root audit: SeparatedScatteredRepresentation 7 (off-support a.e.
pointwise dyadic representation of the scattered field and of the kernel
operator on the enclosing ball), ShellReactionIdentification 8 (the central
identification: coordinates of the reaction operator are almost everywhere the
square-root weight times the integral of the literal shell reaction kernel
against the inclusion source; Riesz functional form plus Fubini on the compact
annulus-times-ball; no Bochner integral in L2 needed). Root author, final
objects and reviews, modal audits requested at the time of writing:
SourcePairedInclusion 10 (paired shell: inner/outer vanishing, unit block,
disjointness, reduction instantiated with the inclusion radius) and
SourcePairedReduction 11 (`eventually_reaction_eq_core`: for large shell index
the paired-shell reaction operator EQUALS the clamped paired-core operator;
hence it converges in operator norm to the central-inversion limit; if the
limiting effective block `volumeBlock ci 1 b - limitingOperator` is a unit,
eventually the effective and combined blocks are units and effective inverses
and solutions converge; the limiting block is a unit when
`errorBound ci 1 b + ‖limitingOperator‖ < 1`). Both were independently audited
by the modal subagent before the final commit. SourcePairedSmallness 3 (root
author; modal audit recorded): the limit operator norm is at most the
inclusion contrast bound times the carrier volume times the sum of the nine
limit-kernel sup norms, so inclusion-data smallness makes the limiting
effective block a unit and eventually the combined blocks are units.

## Second continuation (same day): physical source symmetry closed on the invariant sector

Root (modal Sol audits): SourcePairedWallKernel 5 and its almost-everywhere
twin SourcePairedWallKernelAE 5 with HalfTurnReactionBridgeAE 3 (on the
proper-half-turn-invariant source sector the clamped central-inversion limit
operator equals the gain combination q^(2n)-1, q^(-2n)-1 of the wall-reflection
parity reaction operators, so the limiting effective block IS
`ParityMaterialField.block d 1 (q^n)`), SourcePairedParityLimit 2,
SourcePairedParityClosure 4. Modal Sol (root audits): HalfTurnVectorAction 32
and HalfTurnParityEquivariance 15: the natural half-turn action on vector L2
commutes with the square-root multiplier of a symmetric coefficient, the parity
reaction operators, the dynamic remainder sandwich, the vector Fourier
transform (Schwartz density), the longitudinal multiplier and hence the
physical projection and the whole parity block; the parity solution of
half-turn-fixed data is half-turn fixed with almost-everywhere invariant source.
Fredholm Sol (root audits): SourcePairedSmallInclusion 8 (smallness automatic
below an explicit radius depending only on gains and contrast cap),
SourcePairedSolutionFormula 2 (eventual explicit combined solution),
SourceRemotePlaneFlux 6 (single TM mode exterior plane flux density bounded by
C/|x|^3; scope note `reviews/remote_annulus_return_flux_scope_2026_10_24.md`).
Fredholm Sol (root audits): SourceRemotePlaneFluxTE 2 and SourceRemotePlaneTail 7
(single-mode TM and TE exterior plane flux outside radius R tends to zero).
Channel Sol (root audits): RestrictedTEDipoleProfile 31, RestrictedTEHalfPlanePositive 4,
RestrictedTEDipoleConcentration 31, RestrictedTEPlaneJets 31,
RestrictedTEConcreteDevice 13. Endpoint
`RestrictedTEPlaneJets.explicit_parity_device_counting`: for the explicit parity
device, an orthonormal input family whose plane jets have the prescribed
tangential form with common half-plane sum p0, and thresholds eta < p0 < delta,
eventually in the shrinking scaling every unit-power element of the span has
passage at least eta and absolute bypass at most delta through the half-plane
section; `RestrictedTEConcreteDevice.concrete_counting` discharges the jet
hypotheses by the frozen band interpolation for distinct points on a line, with
p0 = Vb(rho) * halfPlane / scale > 0 explicit. This is a counted-channel
statement with arbitrarily many channels for the EXPLICIT PARITY DEVICE; it is
not the unrestricted target (no unit throughput of the full scattering map, no
finite-stack Green identification, no even-m labelling, no partner spheres).

Closure theorem of the source branch
(`SourcePairedParityClosure.paired_shell_solutions_tendsto_parity_of_small`):
for a half-turn symmetric inclusion coefficient supported in the ball of radius b
inside the core of the actual paired shells, inclusion-data smallness and
parity smallness, and any half-turn-fixed datum f, the effective inclusion
solutions of the paired shells converge in L2 to the explicit parity-device
solution `ParityMaterialField.solution d 1 (q^n) f`. All hypotheses are
explicit and discharged by the frozen smallness criteria; the only undischarged
physical input is that the datum of interest is half-turn fixed.

## Third continuation (same day): remote return flux beyond single modes

Stage 12 (fredholm Sol, root audits): SourceRemotePlaneBand 18 and
SourceRemotePlaneBandTail 3: for any finite family of TM and TE exterior modes
with complex coefficients, the transverse cancellation (tangential times
tangential is parallel to the position, so its normal component vanishes on the
plane) gives a plane flux density bounded by an explicit constant over the cube
of the distance, and the exterior tails vanish. Root-authored
RestrictedTEHomogeneousCount 5 (modal audit): the explicit parity-device count
extended from the unit sphere to the span by homogeneity.
Stage 13 (channel Sol, root audits): RestrictedTEPartnerBalls 21,
RestrictedTEEvenDatum 8, RestrictedTEPartnerCount 9, RestrictedTEConcreteDoubled 5,
RestrictedTEPartnerSmall 1: the half-turn symmetric doubled (partner-ball)
device; every finite TE input has half-turn-fixed sqrt-chi datum (no sector
hypothesis), so SourcePairedParityClosure applies to the actual channel inputs;
doubled counting with model value 2 p0; parity smallness for small scaling.
Root-authored SourcePairedNormSmallness 4 (modal audit): unit-ness of the
limiting effective block from the remainder operator norm plus the
inclusion-data limit term.
Stage 14 (modal Sol, root audit): BarrierSourceStateBounds 27: exterior radial
state bounds of the source response in the barrier (geometric (s/R)^(l+1)
source-weighted bound), low and intermediate degree regimes, uniform in the
shell index beyond the fixed width.
Stage 15 (fredholm Sol, root audits): SourceAnnulusStateBounds 16 and
SourceAnnulusPlaneFlux 9: annulus energy propagation uniform in the shell
index; the finite-band annulus plane flux of the paired shells tends to zero.
Stage 16 (modal Sol, root audit): BarrierAnnulusStateBounds 11: annulus state
bounds in all three degree regimes by induction over the layers; the barrier
geometric bound holds at every radius beyond the inner radius.
Stage 17 (fredholm Sol, root audit): SourceRemotePlaneUniform 11: exterior
constants uniform in the shell index; the absolute finite-band plane flux
outside the core radius tends to zero with the shell index
(`band_outside_core_flux_tendsto`).

Stage 18 (fredholm Sol, root audit): SourceRemotePlaneSeries 5: decompositions
with summable constants pass to series; conditional on degree-summable per-mode
constants beyond a common shell threshold, the absolute all-degree plane flux of
the paired-shell series outside the core tends to zero.
Stage 19 (channel Sol, root audits): WeightedRemainderSchur 9 (the weighted
dynamic remainder sandwich only sees the kernel on differences of carrier
points: Young bound 9 * bound * L1 mass on any measurable superset of K-K),
RestrictedTEPartnerSmallness 25 (remainder mass quadratic and carrier volume
cubic in the scale; at scales q^(-n) the data term is at most a constant times
the scale, so the limiting effective block is eventually a unit),
RestrictedTEPartnerTransfer 2 (`partner_shell_solutions_tendsto`: for q>1,
every enclosing radius and every finite restricted TE coefficient vector, for
all large n the paired-shell effective solutions converge to the explicit parity
solution with gain q^n of the half-turn-fixed datum).
Stage 20 (modal Sol, root audits): BarrierDegreeFluxConstants 20 and
BarrierDegreeDecomp 36: per-mode decomposition constants explicit in the degree
(factorial decay of the regular value at the inner scale absorbs the low and
intermediate regimes; the barrier regime is geometric beyond an explicit
threshold radius), summable against any polynomial weight with one
degree-independent threshold: the exact interface of the series theorem.
Stage 21 (fredholm Sol, root audit): SourcePairedReactionField 13: the
shell-reaction field at arbitrary points, uniform kernel convergence on product
balls, uniform convergence of the reaction fields on balls for L2-convergent
inclusion solutions, and the identification of the limit field with the parity
plane reaction fields on half-turn invariant sources.
Stage 22 (modal Sol, root audit): BarrierDegreeSeriesFlux 20: the absolute
plane flux outside the core of the all-degree, all-mode paired-shell series with
bounded coefficient families tends to zero with the shell index (modes encoded
by the natural numbers with extension by zero).
Stage 23 (channel Sol, root audits): ChannelCesaroThroughput 5,
ChannelScaledFields 30, ChannelFarFluxExpansion 11, ChannelUnitThroughput 9,
ChannelAntipodalAmplitude 4: unit throughput of the complete lossless field for
finite TE incident fields at unit frequency; the sphere flux is constant in the
radius while its exact far expansion is a convergent part plus exp(-2ir) times a
convergent coefficient, and an interval average over the radius forces the
outgoing energy (outgoing incident amplitude plus scattered far amplitude) to
equal the incoming energy; the weak-Maxwell pair and the exterior representation
of the actual device are hypotheses, satisfied in vacuum.
Stage 24 (fredholm Sol, root audit): SourcePairedPlaneCompact 25: the
finite-shell effective block commutes with the half-turn; the assembled plane
electric field of the effective solutions converges uniformly on balls at
positive distance from the carrier to the parity-device total electric field.
Stage 25 (modal Sol, root audit): BackgroundCoreTransmission 46: the background
lift at the radial level (Wronskian transport of a unit incoming wave to 2i/c2
times the regular core state, convergence of the transmission along the radii
2 pi (s+1), datum convergence of the rescaled finite TE vector, the layered
background state as -(conj c2) times the source state minus its conjugate).
Stage 26 (channel Sol, root audits): ChannelMaterialThroughput 8 and
ChannelScatteringMap 19: the volume solution of any bounded dielectric with a
finite TE incident field is a weak Maxwell pair with the exterior
incident-plus-dyadic representation, so the actual paired shells plus inclusion
have unit throughput whenever the effective block is a unit, and the scattering
map on the finite TE input space is linear and isometric.
Stage 27 (channel Sol, root audits): RestrictedTEActualCounting 19 and
RestrictedTEActualWindow 15: the diagonal assembly and the manuscript's
counted-subspace form for the actual paired device, for every N, every window
0 < eta < delta and every tau at most one: an orthonormal family of N finite TE
inputs whose span is a counted subspace with unit transmission, for every
quadratically homogeneous actual flux family satisfying the whole-plane L1
interface (`L1Interface`), which is the single remaining hypothesis on the
device's flux (the identification of that family with the actual Poynting flux
and its L1 convergence to the parity flux).
Stage 28 (fredholm Sol, root audit): SourcePairedPlaneMagnetic 50: the magnetic
shell reaction field and the assembled plane magnetic field converging on
compacts to the parity-device total magnetic field.
Stage 29 (channel Sol, root audit): RestrictedTEActualSquare 16: the
counted-subspace statement through one fixed square (device on the left edge,
N points on a fixed segment) with the dielectric proved to lie in
[1, eps_plus]: for every eps_plus > 1, N, window 0 < eta < delta, tau at most
one and square half-side there are an ordinary dielectric in [1, eps_plus] and
an orthonormal family of N finite TE inputs whose span is a counted subspace,
for every quadratically homogeneous actual flux satisfying the whole-plane L1
interface. This is the manuscript's uc:counterexample form modulo that
interface.
Stage 30 (modal Sol, root audits): BackgroundModeMaxwell 68,
BackgroundModeResponse 27, BackgroundModeTE 56: the background mode is a
global weak Maxwell field (conjugation symmetry of forced pairs) whose
scattered part radiates, so by the representation theorem and the unit shell
block the shells' actual response to each regular TM mode and to every finite
TE coefficient vector is the background mode, whose core part is
transmission/2 times the incident field, converging along the radii
2 pi (s+1): the background lift (a) is complete at the single-shell level.
Stage 31 (channel Sol, root audit): RestrictedTEL1Assembly 18: the whole-plane
L1 interface reduces to measurability, compact convergence on disks and
inverse-cube tail majorants of the actual and parity fluxes; the parity flux
has the majorant (six audited piece tails through the mixed identity), is
integrable and quadratically homogeneous.
Stage 32 (modal Sol, root audits): BackgroundShellCoefficient 16 and
BackgroundFluxMajorant 30: the material pipeline depends on a coefficient only
through its value, so the mu-material TE response is the response of the
closure theorem's shell coefficient; the background plane flux of a finite TE
vector has an inverse-cube majorant uniform in the shell index in the core,
annulus and exterior.
Stage 33 (fredholm Sol, root audit): SourcePairedPlaneIdentification 51: the
assembled plane fields are the fields of the combined shell-plus-inclusion
solution inside the core (dipole superposition, block decomposition, effective
datum = datum of the background field on the inclusion, a.e. identification on
the gap annulus), and the combined total fields converge on compacts to the
parity device under converging background and effective data.
Stage 34 (channel Sol, root audit): RestrictedTEActualFields 18: the counted-
subspace theorem through the fixed square for every pair of linear plane field
families satisfying the actual field estimates (measurability, uniform
convergence on disks to the parity fields, inverse-cube tail majorant).
Alignment point found by root at this stage: the actual device's limit incident
field is the physical input rescaled degreewise by half the limiting
transmission, while the parity device's incident is the input times q^n; the
even-degree limiting transmission (modulus q^n by the even gamma limit) must be
computed exactly, and any degree-dependent unimodular phase absorbed into the
input family by a unitary twist (in progress).
Stage 35 (channel Sol, root audit): RestrictedTEActualCore 82: the inside-core
actual fields of the paired device from the combined solution are linear and
measurable, the shell background on the open core is the incident field
rescaled degreewise by half the transmission, the effective datum converges to
the half-turn-fixed limiting datum, the fields converge uniformly on disks to
the raw limit, and with the limiting rescaling equal to q^n times a unitary
twist the counted-subspace theorem holds for the untwisted interpolation
family from core agreement, the tail majorant and the twist identity.

In progress at this commit (author drafts, untracked until audited):
CoreRadiatedMajorant with its Core* companion files and
BackgroundTransmissionParity (modal Sol; the radiated field's inverse-cube
majorant in the growing core; the even/odd limiting transmission and the
twist), SourceRadiatedSeries (fredholm Sol; the radiated field outside the core
as the layered mode series with moment coefficients), RestrictedTEActualPiecewise
(channel Sol; piecewise fields, tail assembly from the core and outside
majorants, solution bounds on the unit sphere, final composition).

Remaining analytic work for the L1 interface, all now assigned: the actual
flux must be defined piecewise (kernel integrals inside the core, the layered
mode series with moment coefficients outside, where the dyadic integral is only
an L2 class inside the shell material); the mode-series representation of the
radiated field outside the core (coefficients = source moments); the
inverse-cube majorant of the radiated field inside the growing core (in
progress); the background majorant is done (stage 32).

## What this does and does not establish

The finite-shell-plus-inclusion reduction is formalized end to end and tied to
the channel branch's explicit parity device on the half-turn-invariant sector,
with every module independently audited. It does NOT establish: the all-degree
remote return flux (finite-band annulus and exterior plane flux outside the
core vanish with the shell index, uniformly in the shell; the degree sums are
in progress), the unrestricted counted-channel theorem (the parity-device count
is proved; unit throughput of the full scattering map and the finite-stack Green
identification of the parity flux with the paired-shell flux remain), any modal
statement (blocked by Hermite-Lindemann and a
complex-frequency radiation representation absent from the tree), or
uniform-in-k hotspot input. Full OQ14 closure remains open; see
`reviews/closure_assessment_2026_10_24.md`.

## Immediate next work (in order)

1. Audit and record the in-progress drafts as they land (CoreRadiatedMajorant and
   companions, BackgroundTransmissionParity, SourceRadiatedSeries,
   RestrictedTEActualPiecewise);
   every audited module so far is recorded; the last tag is
   `oq14-resume-2026-10-24-2`, third-continuation commits: `be89c03`, `d0ec870`, `96ffdba`, `874160c`, `e0c1858`, `920914d`, `bd9a349`, `2d90be0`, `3412885`, `e591113`, `830b8e6`, `396e899`, `48bd956`, `67f92cf`, `a3e59ea`, `e9170ec`, `49a4ff4`, `6cc8945`, `0c546d3`, `9fbb710`, `a160c71`, `90d1f3f`, `2e1972a`, `83d0b2f`, `40b3aea`, `c4f141b`, `badccfa`, `b3e9f84`, `781acf3`, `30e1ee0`, `12e11c5`, `83548bc`, `a5aa7c0`, `d20add2`.
2. Bridge items (a)-(f) listed at the end of the third-continuation section,
   in that order; (a) and (b) go to the modal author after the series assembly,
   (c)-(e) to the fredholm author after the compact plane field, (f) is with the
   channel author.
3. Channel afterwards: closed form halfPlane = 1/(2 pi h), bounded symmetric
   section for the doubled device.
4. Record scripts `tmp/record_after_5238.py` and `tmp/record_modal_after_5238.py`
   now accept primed theorem names (regex widened on 2026-10-24).
5. Modal: see the scope note; the fixed input remains per-frequency.

## Handoffs and how to resume safely

October 23 handoffs remain valid historical records
(`reviews/modal_checkpoint_2026_10_23_stop.md`,
`reviews/fredholm_sol_stop_oct23_fixed_angular.md` (+ JSON),
`reviews/continuation_uniform_stop_2026_10_23.md`). Today's per-module author
reviews and independent receipts are under `reviews/` by snake-case module
name; scope notes are `reviews/*_scope_2026_10_24.md`.

Process that worked today: Sonnet ("6.1 Sol") subagents author and repair
drafts, one Lean process each; root (Astra) keeps the critical mathematics,
audits everything from source with fresh compiles, records receipts with
`tmp/record_after_5238.py` (root audits; logs `lean/logs/<M>-root-audit.log` +
`.exit.log` containing `0`) or `tmp/record_modal_after_5238.py` (non-root
audits of root modules; logs `lean/logs/<M>-modal-audit.log`; receipt
`reviews/<m>_independent.md` must contain PASS, exit 0 and both hashes), and
alone touches Git. Never rerun the one-time `integrate_current_audits.py 5238`
or older checkpoint/release creators. Git checkpoints today: `f2cb699`,
`b6f653b`, `f37b0b4`, `4d3066c`, `e612292`, `fe2e75e`, `926ee8a` (tag
`oq14-resume-2026-10-24`), `a5f0156`, `eaadf5c`, `f8b3dc3`, then the final
commit of the second continuation; `tmp/` and `*.log` are gitignored, so evidence is
copied under the checkpoint folder and added with `git add -f` (add
directories, not globs: the Windows argument limit rejects large globs). Never
stage `sites/`.

Workspace: D:/oq14. Compile with cwd D:/oq14/lean using
D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe
(`lake.exe env lean <Module>.lean` for a check, `-o .lake/build/lib/lean/<Module>.olean`
for the final object). Always run inside `( cd /d/oq14/lean || exit 9; ... )`:
the Bash tool's working directory drifts between calls and a compile started
from the wrong directory fails to find the project search path. The aggregate
`Mathlib` module is not built; import specific Mathlib files. Section variables
used only in proofs must be `include`d; generic-ring lemmas should be applied to
named `def`s to avoid definitional-equality blowups against concrete operator
terms. Lean 4.19.0; mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; nine
pins. Small modules compile in 10–60 s. Never clean root lean/.lake/build;
never compile a dependent before its dependency has a passing final object;
use explicit UTF-8 reads (logs may have UTF-16 BOM). Memory is tight on the
machine; keep concurrent Lean processes to about three.

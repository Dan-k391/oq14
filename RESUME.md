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
compiled modules: 254 modules / 1696 reports at the latest third-continuation
commit `e9170ec` (226 / 1334 at the end of the second continuation, 169 / 832 at
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

In progress at this commit (author drafts, untracked until audited):
BackgroundCoreTransmission (modal Sol; background lift: transmitted core
amplitude 2i over the second shell coefficient, its phase-normalized limit, and
datum convergence by linearity), ChannelMaterialThroughput (channel Sol;
discharging the weak-Maxwell pair and exterior representation for the material
volume solution, at gain one the parity block is the plain volume block, and the
linear isometric scattering map), SourcePairedPlaneMagnetic (fredholm Sol; the
magnetic shell reaction field, its compact limit through the first-order jet
limits, and the curl analogue of the central-equals-wall identity).

Remaining bridge to the physical dielectric, in order: (a) background lift
(incoming-to-core multiplier convergence of the finite-band incident family with
the phase choice radius s = 2 pi (s+1), so the closure datum is the actual
core background field); (b) identification of the all-degree radiated field
outside the core with the mode series (coefficients = source moments, bounded
by the regular value at the inclusion scale); (c) the magnetic plane field and
its compact convergence, and the identification of the assembled plane field
with the combined shell-plus-inclusion solution (operator/integral interchange);
(d) whole-plane L1 convergence of the paired-shell
plane flux to the parity-device flux (compact part from (c), remote part from
BarrierDegreeSeriesFlux, parity tail by integrability); (e) the diagonal choice
of the shell index as a function of n and the counting statement for the
actual device; (f) unit throughput. The modal theorem stays blocked by
Hermite-Lindemann.

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

1. Audit and record the in-progress drafts as they land (BackgroundCoreTransmission,
   ChannelMaterialThroughput, SourcePairedPlaneMagnetic);
   every audited module so far is recorded; the last tag is
   `oq14-resume-2026-10-24-2`, third-continuation commits: `be89c03`, `d0ec870`, `96ffdba`, `874160c`, `e0c1858`, `920914d`, `bd9a349`, `2d90be0`, `3412885`, `e591113`, `830b8e6`, `396e899`, `48bd956`, `67f92cf`, `a3e59ea`, `e9170ec`.
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

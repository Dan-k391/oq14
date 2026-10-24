# OQ14 resume state — October 24, 2026 (fourth continuation: frequency scaling)

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
compiled modules: 297 modules / 2759 reports at the stage-49 commit
`f4d5564` of the fourth continuation (292 / 2704 at the end of the third
continuation, commit `03d765b`; 226 / 1334 at the end of the second; 169 / 832 at
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
Stage 36 (channel Sol, root audit): RestrictedTEActualPiecewise 30: piecewise
device fields (core inside the inner shell radius, abstract outside), the tail
from core and outside majorants, the outside majorant from uniform
decompositions of background plus radiated parts, the background decomposition
on the unit sphere of the span, eventual boundedness of the inclusion
solutions, and the composite counted-subspace theorem under the remaining
analytic hypotheses (outside fields, radiated decomposition, core majorant,
twist identity).
Stage 37 (modal Sol, root audits): CoreWeakSeries 8, CoreWeakLinear 5,
CoreOutgoingModes 22, CoreFreePotential 21, CoreReactionDegree 5,
CoreRegularModes 10, CoreReaction 23, CoreRadiatedMajorant 7: the radiated
field of the inclusion decomposes inside the growing core with constants
independent of the shell index (moment series of the vacuum modes for the free
potential, degree series of regular modes for the shell reaction, the degree
bound on the reaction coefficient times regular state times moment factor), so
the assembled plane flux has an inverse-cube majorant between a fixed radius
and the inner shell radius: the core majorant hypothesis of stage 36 is
discharged.
Stage 38 (fredholm Sol, root audits): SourceRadiatedSeries 32,
SourceRadiatedMagnetic 45, SourceRadiatedFlux 28: the radiated field of the
inclusion (free potential plus shell reaction) is the series of source moments
times the layered TM and TE modes beyond the stack radius, electric and
magnetic; the series flux theorem generalized to shell-dependent coefficients
and TE-chain data; the exterior plane flux of the actual radiated field
vanishes with the shell index for bounded inclusion solutions. The shell
annulus (inner radius to stack radius) is not yet identified.
Stage 39 (modal Sol, root audit): BackgroundTransmissionParity 38: half the
limiting TE transmission is q^n times the global unimodular parity phase
exp(i n pi (q-1)/(2q)) on even degrees (q^(-n) on odd degrees); the
degreewise rescaling of even-supported vectors is q^n times a unitary global
phase twist, so the alignment of the actual limit incident with the parity
incident holds with an n-dependent global phase, which leaves spans,
orthonormality and all quadratic flux functionals unchanged.
Stage 40 (modal Sol, root audit): ExteriorMaterialOffCarrier 10: the Newton
identity on an arbitrary open set where the source vanishes (separation
pairing, countable ball cover), so the physical L2 total field of the combined
solution equals the assembled plane electric field almost everywhere on the
core outside the closure of the inclusion carrier.
Stage 41 (modal Sol, root audit): CoreMajorantDevice 13: the core-majorant
structure of the piecewise assembly is discharged for the concrete doubled
device (background family plus radiated decomposition plus eventual solution
bound on the unit sphere), with the magnetic core formula of the background
family.
Stage 42 (channel Sol, root audits): RestrictedTEBackgroundOutside 53 and
RestrictedTEActualPhase 23: the TE background pair equals the actual total
fields of the shell solution (magnetic pointwise off the origin by weak
uniqueness and continuity, electric beyond the stack radius and a.e. in the
annulus); the outside background plane fields and the outside decomposition
reduced to the radiated part; the device fields depend on the input only, so
the assembly works with the n-dependent global unimodular parity phase.
Stage 43 (channel and fredholm Sol, root audits): RestrictedTEParityInstance 2
and SourceRadiatedAnnulus 34: the counting theorem with the parity phase and
the discharged core majorant carries only two hypotheses on the radiated plane
fields (measurability and the uniform decomposition beyond the inner shell
radius); the radiated field of the inclusion equals the layered mode series
almost everywhere on the whole region beyond the inner shell radius (weak route
through bounded pairing functionals and the fundamental lemma), with the
uniform decomposition export, plane measurability and linearity in the
inclusion solution: every analytic hypothesis of the assembly is now proved.
Stage 44 (channel Sol, root audit): RestrictedTEActualDevice 17:
`actual_counted_subspaces_device`, the counted-subspace theorem for the actual
paired dielectric device with no field hypotheses: for every eps_plus > 1,
every N, every window 0 < eta < delta, every tau at most one and every square
half-side there are device parameters and an orthonormal family of N finite
TE inputs such that the paired device's dielectric lies in [1, eps_plus] and,
eventually in the gain and shell indices, the span is a counted subspace
through the fixed square (exact unit transmission by the isometric scattering
map, passage at least eta, bypass at most delta) for the plane flux of the
piecewise device fields; the theorem depends only on propext,
Classical.choice and Quot.sound. The piecewise device fields are the physical
fields almost everywhere in space on the core off the carrier (stage 40) and
beyond the inner shell radius (stages 38, 42, 43); the consolidated statement
of these identifications is stage 45.
Stage 45 (modal Sol, root audit): PhysicalFieldIdentification 39: the physical
fields of the combined shell-plus-inclusion device (the L2 total electric field,
its continuous exterior representative, the pointwise total magnetic field) are
the space versions of the piecewise fields of the assembly: the L2 electric
field almost everywhere on the open core off the carrier closure, on the shell
annulus and on the exterior, the continuous representative at every point
beyond the outer radius, the magnetic field at every point of the open core and
of the exterior and almost everywhere in space; eventually in the shell index,
with no hypothesis on the annulus (predicate `PhysicallyIdentified`);
instantiated for the concrete doubled device eventually in the gain index, and
the piecewise device fields of the assembly are these space versions at every
plane point whenever the outside radiated plane fields are the radiated series.
Stage 46 (modal Sol, root audit): PhysicalDeviceFields 4: beyond the threshold
shell index and strictly beyond the inner radius the radiated plane fields of
the device module are the radiated series of the identification module, so
the exact piecewise device fields counted by
`RestrictedTEActualDevice.actual_counted_subspaces_device` equal the space
versions of the physical fields at every plane point off the inner circle and
for almost every plane point, eventually in the gain and shell indices
(`device_fields_physical`, `device_fields_physical_ae`). The
field-identification chain of the channel branch is complete.

Fourth continuation (same day): the unit-frequency caveat removed by scale
invariance (design note `reviews/frequency_scaling_design.md`).
Stage 47 (channel Sol authors, root audits): FrequencyScalingMaxwell 23,
FrequencyScalingFlux 12, FrequencyScalingPower 8: the frozen weak dielectric
system `MaterialMaxwell.TestMaxwell` is scale invariant (dilated compact smooth
tests, Jacobian k^-3, chain rule k^-1: `TestMaxwell 1 ε E H` gives
`TestMaxwell k` for the coefficient `scaleCoeff k c` with value at k x and the
same bounds, and for the amplitude-normalized dilated fields
`scaleField k F x = k F (k x)`); the plane flux density of dilated field maps is
k^2 times the original at k ξ, the square and its complement dilate exactly,
passage and bypass through `Dsq L` of the dilated fields equal those through
`Dsq (k L)` of the originals, so `IsCounted` transfers with the same scattering
map, power and thresholds (`isCounted_scale`); the inward sphere power of the
dilated finite TE incident pair at radius r is the unit-frequency power at
radius k r and tends to `physicalPower`, the dilated incident pair is a vacuum
weak Maxwell pair at frequency k, and the far amplitude is unchanged
(`factor k r * k = factor 1 (k r)`).
Stage 48 (channel Sol author, root audit): FrequencyScalingDevice 6: the
physical fields `physE`, `physH` of the combined shell-plus-inclusion solution
satisfy `TestMaxwell 1` with the dielectric of the combined coefficient whenever
the combined block is a unit, hence for the concrete doubled device eventually
in n and r (a statement not previously written down for the combined device);
the dilated fields satisfy `TestMaxwell k` with the dilated coefficient; the
stage-45 identification transports along the dilation (`PhysicallyIdentifiedAt`,
radii divided by k, almost-everywhere clauses by the quasi-measure-preserving
dilation), and the dilated piecewise plane fields of the final counting theorem
are the dilated space fields at every plane point off the circle of radius
`radius r / k`.
Stage 49 (channel Sol author, root audit): RestrictedTEFrequencyScaling 6:
`counted_subspaces_at_frequency`: for every k > 0, eps_plus > 1, N,
0 < eta < delta, tau <= 1 and half-side L > 0, the unit-frequency device of
half-side k L with coefficient `scaleCoeff k (pairedCoeff …)` (the device
dilated by 1/k: shells of radii R_r/k, X_r/k, spheres of radius ρ a_n/k at
height h a_n/k above the points (-L, y_l), `devPos_scale`) has dielectric
values in [1, eps_plus], the same orthonormal family of N finite TE inputs has
a span that is, eventually in n and r, a counted subspace through the square
`Dsq L` for the plane flux of the dilated device fields `scaleMap k deviceFieldsE/H`
with the same scattering map `actualScatter`, the same `physicalPower` and the
same tau, eta, delta; the dilated finite TE inputs are vacuum weak Maxwell
pairs at frequency k with limiting inward power `physicalPower`; and eventually
in n, for every input, eventually in r, the dilated physical fields are a weak
Maxwell pair at frequency k with the dilated dielectric, identified with the
dilated space fields, whose plane values off the circle of radius `radius r / k`
are the counted plane fields. Standard axioms only. Not asserted: that the
dilated fields are the volume solution `MaterialField.total (scaleCoeff k c) k …`
of a dilated L2 datum (no dilation of the L2 machinery and no uniqueness at
frequency k are in the tree; design note section 5).
Stage 50 (channel Sol author, root audit): CountedSubspacesManuscript 3: the
manuscript-form corollaries with explicit indices (no eventual quantifiers):
`counted_subspaces_manuscript`: for k > 0, eps_plus > 1, 0 < eta < delta,
0 < tau < 1 and side L fixed before N, every N has a single finite device
(explicit gain index n and shell index r) with dielectric in [1, eps_plus], an
orthonormal family of N finite TE inputs whose span is a counted subspace
through the open square (-L/2, L/2)^2, unit throughput of the scattering map on
every finite TE input, and the per-basis-vector physical identification at
frequency k; the docstring maps the clauses to uc:counterexample and lists what
is not asserted. Rates in n and r are not needed for the manuscript's
existential statement; they remain unproved.

Stage 51 (modal Sol, root audit): DilationKernels 24: the Green kernel
identities for k > 0 (phi_k(x) = k phi_1(k x), gradient k^2, Hessian and
dyadic/remainder kernels k^3, static Hessian k^3) and, by change of variables,
the remainder response and the magnetic response to the dilated source
k rho(k .) are k times the unit-frequency responses at k x.
Stage 52 (fredholm Sol, root audit): DilationL2 49: the dilation operator
D_k u = k u(k .) on the weighted vector L2 space (exact inner-product identity
<D_k u, D_k v> = k^-1 <u, v>, group laws), commuting with the square-root
multiplier of the dilated coefficient; the dilated source almost everywhere; the
Fourier intertwining F(D_k u) = k^-1 D_(1/k) F u (Schwartz change of variables,
density); hence the longitudinal projection, the Newton operator, the static
response and the static Newton block commute with D_k, and the physical
coordinate dilates with the factor k almost everywhere.

Stage 53 (modal Sol, root audit): FrequencyFieldResponse 9: the scattered and
total electric fields of the dilated coefficient and dilated weighted field at
frequency k are the dilations k E(k x) of the unit-frequency fields almost
everywhere, the total magnetic field at every point; the dilated coefficient
of a sum; the weighted-datum predicate transported.
Stage 54 (fredholm Sol, root audit): DilationVolume 35: the truncated remainder
kernel at frequency k and radius R/k is k^3 times the unit kernel at k z, its
Fourier transform is the unit transform at xi/k, the scalar dilation
intertwines the Fourier-side convolution operators, and the dynamic
convolution operator, the weighted remainder and the dynamic volume block of
the dilated coefficient at radius R/k commute with D_k; the error bound is
invariant; the block at frequency k is the conjugate of the unit-frequency
block, so units and Ring.inverse transport and
solution (scaleCoeff k c) k (R/k) (D_k f) = D_k (solution c 1 R f) with no
smallness hypothesis.
Stage 55 (modal Sol, root audit): FrequencyVolumeSolution 12: for the combined
device and every k > 0 the rescaled physical fields are the frequency-k
MaterialField.total (almost everywhere) and totalMagnetic (at every point) of
the frequency-k volume solution, at radius X/k, of the dilated paired
coefficient with the rescaled incident field and the dilated total datum,
which is the weighted datum of the rescaled incident field; the dilated block
is a unit exactly when the unit-frequency block is
(`dilated_fields_are_volume_solution`). The dilation caveat of stages 47-49
is removed at the level of the fields.
Root note (draft, unverified): reviews/modal_item2_degeneration_note_2026_10_25.md
sketches a transcendence-free route to the all-degree pole isolation of the
modal branch (degeneration of the index to 1 against the polynomial growth of
an algebraic coincidence branch); the closure assessment's (C) paragraph now
states the modal block precisely (items 1 and 3 remain large).

Stage 56 (channel Sol, root audit): CountedSubspacesVolume 2:
`counted_subspaces_at_frequency_volume` and `counted_subspaces_manuscript_volume`,
the frequency-k counting theorem and its manuscript form verbatim, with the
identification clause extended by the stage-55 summary: for every input
(eventually in r) and for every basis vector (at the explicit indices) the
rescaled physical fields are the frequency-k material total fields of the
frequency-k volume solution at radius X/k of the explicit dilated dielectric
with the rescaled incident field, whose weighted datum is the dilated datum,
and the dilated block is a unit iff the unit-frequency block is. The dilation
caveat of the frequency statement is removed; the docstring lists what is
still not asserted (finite even-degree TE inputs; flux integrability inside
IsCounted; identification in space with continuous plane representatives off
the circle; the flux normalization; no rates; the solution map is Ring.inverse
of the block, whose unit-frequency invertibility for the device is the frozen
development's).

In progress at this commit: nothing; every delivered module is audited and
recorded, and no brief is outstanding.

What the channel branch now establishes in Lean: the manuscript's
uc:counterexample form for the actual paired dielectric (ordinary dielectric
in [1, eps_plus], fixed square, fixed thresholds, every N), with the flux of the
piecewise device fields, which are the physical fields of the combined
shell-plus-inclusion solution (stage 45, `PhysicallyIdentified`: the L2 electric
field almost everywhere in space off the carrier closure and the inner sphere,
the magnetic field almost everywhere in space and pointwise on the open core
and the exterior), and by stage 46 the exact fields counted by the final
theorem are these space versions at every plane point off the inner circle
and for almost every plane point. By stage 49 the same statement holds at every
frequency k > 0 in the dilation sense (`counted_subspaces_at_frequency`: dilated
coefficient, dilated fields satisfying the weak Maxwell system at frequency k,
same scattering map, power and thresholds, square of half-side L), and by stage 50 in the manuscript's literal form
(`CountedSubspacesManuscript.counted_subspaces_manuscript`: one finite device per
N with explicit gain and shell indices, square (-L/2, L/2)^2, 0 < tau < 1,
0 < eta < delta, unit throughput), and by stage 56 with the frequency-k fields
identified with the frequency-k material solution of the explicit dilated
dielectric (`CountedSubspacesVolume.counted_subspaces_manuscript_volume`). Caveats that
remain and are stated in reviews/channel_actual_counting_scope_2026_10_24.md:
finite even-degree restricted TE inputs; the open square up to parametrization;
all statements eventual in the gain index n and the shell index r without
rates; the identification is in space, not almost everywhere on the plane (the
plane fields are the continuous representatives). The modal branch (C) remains
blocked by Hermite-Lindemann; the hotspot branch (B) keeps its per-frequency
input. Full OQ14 closure is therefore still not claimed.

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
uniform-in-k hotspot input. The channel counting theorem holds at every
frequency k > 0 in the dilation sense of stage 49 (what is and is not asserted:
`reviews/frequency_scaling_design.md`, section 5). Full OQ14 closure remains
open; see `reviews/closure_assessment_2026_10_24.md`.

## Immediate next work (in order)

1. The channel branch is complete through the physical-field identification
   (stages 16-46) and holds at every frequency k > 0 in the dilation sense
   (stages 47-49); the tag `oq14-resume-2026-10-25-1` marks the stage-49
   refresh commit (fourth-continuation commits `ebbb006`, `340dcf3`,
   `f4d5564`).
   Stage 50 (`CountedSubspacesManuscript`, commit `d8a3e97`) gives the
   manuscript's literal form (explicit indices, square (-L/2, L/2)^2), which
   settles (b) and shows that rates are not needed for the manuscript's
   existential statement. (c) The identification of
   the dilated fields with the frequency-k volume solution is proved by the
   constructive dilation route (stages 51-55: DilationKernels, DilationL2,
   FrequencyFieldResponse, DilationVolume, FrequencyVolumeSolution; no
   uniqueness theory: every operator of the volume block conjugates by the
   dilation D_k u = k u(k .) because the dyadic kernel satisfies
   G_k(z) = k^3 G_1(k z)), and the counting theorems are restated with that
   clause (stage 56, CountedSubspacesVolume). The tag
   `oq14-resume-2026-10-25-2` marks the stage-56 refresh commit. Nothing is
   assigned. Still optional: (a) explicit thresholds or rates in n and r (not
   needed for the manuscript's existential statement). The modal branch (C):
   see the draft degeneration note; the honest status is that it needs either
   a transcendence input or that unverified analysis, plus two large analytic
   items; not assigned. Every
   audited module is recorded; earlier tags `oq14-resume-2026-10-24-3`,
   `oq14-resume-2026-10-24-2`,
   third-continuation commits: `be89c03`, `d0ec870`, `96ffdba`, `874160c`, `e0c1858`, `920914d`, `bd9a349`, `2d90be0`, `3412885`, `e591113`, `830b8e6`, `396e899`, `48bd956`, `67f92cf`, `a3e59ea`, `e9170ec`, `49a4ff4`, `6cc8945`, `0c546d3`, `9fbb710`, `a160c71`, `90d1f3f`, `2e1972a`, `83d0b2f`, `40b3aea`, `c4f141b`, `badccfa`, `b3e9f84`, `781acf3`, `30e1ee0`, `12e11c5`, `83548bc`, `a5aa7c0`, `d20add2`, `409cd12`, `42446f9`, `d8c0197`, `513ded8`, `8ae8281`, `3c5beef`, `ba118ff`, `738a361`, `86237a5`, `bf235ac`, `ff74c55`, `7f1cb3a`, `d156d79`, `a2fd08b`, `8e04cd0`, `7c667c1`, `d3c2a6e`, `4d50464`, `4febdea`, `e7b81e6`, `ea163dd`, `03d765b`.
2. The bridge items of the earlier continuations are all done (stages 16-46);
   nothing from them is open.
3. Channel, optional: the closed form halfPlane = 1/(2 pi h); the fixed square
   (`RestrictedTEActualSquare`) already supplies the bounded section used by the
   final theorem, so this is cosmetic.
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

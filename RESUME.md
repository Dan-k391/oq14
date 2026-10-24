# OQ14 resume state — October 24, 2026 (end of the second continuation)

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
compiled modules: 226 modules / 1334 reports at the final commit of the second
continuation (169 / 832 at the October 23 stop).
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

## What this does and does not establish

The finite-shell-plus-inclusion reduction is formalized end to end and tied to
the channel branch's explicit parity device on the half-turn-invariant sector,
with every module independently audited. It does NOT establish: the remote
annulus whole-plane return flux (only single-mode exterior density bounds and
tails exist), the unrestricted counted-channel theorem (the parity-device count
is proved; unit throughput of the full scattering map and the finite-stack Green
identification of the parity flux with the paired-shell flux remain), any modal
statement (blocked by Hermite-Lindemann and a
complex-frequency radiation representation absent from the tree), or
uniform-in-k hotspot input. Full OQ14 closure remains open; see
`reviews/closure_assessment_2026_10_24.md`.

## Immediate next work (in order)

1. Nothing is pending: every module added in both continuations is
   independently audited and recorded. Tags: `oq14-resume-2026-10-24` (end of
   the first continuation) and `oq14-resume-2026-10-24-2` (final commit).
2. Remote annulus return flux: the TE dual, the integrated plane tail, then
   finite-band sums and the all-degree uniform state bounds (scope note).
3. Channel: unit throughput / power normalization of the full scattering map
   (Riemann-Lebesgue cross-term step), partner spheres, extension from the unit
   sphere to the span by homogeneity, closed form halfPlane = 1/(2 pi h).
4. Tie the parity device input (RestrictedTE datum) to a half-turn-fixed
   datum so that SourcePairedParityClosure applies to the actual channel
   inputs; identify the parity plane flux with the paired-shell total-field
   plane flux (needs the remote annulus bound).
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

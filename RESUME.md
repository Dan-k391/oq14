# OQ14 resume state — October 24, 2026 (end of the resumed session)

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
compiled modules: 208 modules / 1130 reports at the time of writing (169 / 832
at the October 23 stop).
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
author, final; modal audit requested): the limit operator norm is at most the
inclusion contrast bound times the carrier volume times the sum of the nine
limit-kernel sup norms, so inclusion-data smallness makes the limiting
effective block a unit and eventually the combined blocks are units.

## What this does and does not establish

The finite-shell-plus-inclusion reduction announced as "next" on October 23 is
now formalized end to end (modulo the two pending modal audits): the actual
combined paired-shell-plus-inclusion volume equation reduces exactly to the
shell block and an effective inclusion equation whose operator is literally the
clamped paired-core operator for large shell index, and inverse stability
transfers along the central-inversion limit. It does NOT establish: the physical
source symmetry (the limit is central inversion; the parity device uses wall
reflection; equality holds only in the proper-half-turn-invariant source sector,
`HalfTurnReactionBridge`), the remote annulus whole-plane return flux, an
explicit bound on the limit operator norm, the complete scattering output, any
channel count, or any modal statement. Full OQ14 closure remains open.

## Immediate next work (in order)

1. Record the modal audit of SourcePairedSmallness if it was not recorded
   (`tmp/record_modal_after_5238.py SourcePairedSmallness`), copy its log under
   the checkpoint evidence and commit.
2. Root: the assembled eventual explicit combined solution formula (per shell
   index it is `ShellInclusionVolume.solution_eq` with
   `SourcePairedInclusion.effective_eq` and the eventual unit property; the
   single assembled statement timed out at elaboration and was dropped from
   SourcePairedSmallness); explicit values or decay of the limit-kernel sup
   norms in the inclusion radius.
3. Root: physical source symmetry — show the material-inverse source of the
   effective inclusion problem lies in the proper-half-turn-invariant sector
   for symmetric inclusions, so `HalfTurnReactionBridge.central_eq_wall`
   identifies the limiting operator with the wall-reflection parity operator of
   `RestrictedTEParitySandwich`; then the channel branch's parity endpoint
   becomes a statement about the actual paired shells. Then the remote annulus
   return flux.
4. Channel: dipole-flux concentration / plane jets (scope note item (iii)(b)),
   then unit throughput.
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
`b6f653b`, `f37b0b4`, `4d3066c`, `e612292`, then the stage 6 commit and any
later audit-recording commit; `tmp/` and `*.log` are gitignored, so evidence is
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

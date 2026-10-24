# OQ14 resume state — October 24, 2026 (work resumed at the user's request)

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
compiled modules. At the time of writing it holds 198 modules / 1060 reports
(it held 169 / 832 at the October 23 stop). Every recorded report uses only
`propext`, `Classical.choice` and `Quot.sound` (some pure-algebra reports use
`propext` alone). "Independently audited" means: a complete-source
mathematical review by someone other than the author plus a fresh pinned
compile from source without the author's object, exit 0, no warnings, with the
receipt `reviews/<module>_independent.md` carrying exact source and log hashes.
Root audits subagent work; the modal subagent audits root work. Author-only
status is always stated as such. These targeted checks are NOT a new release.

## What was done on October 24 (all independently audited unless marked)

Resume stage 1: the seven modules left author-only at the stop were audited
(CompactCoreKernel 7, SourcePairedCore 5, ConicalUniformBall 3,
FiniteAngularNonzero 4, SphereVectorPairing 5, FiniteMixedFields 13,
RestrictedTEFieldLinear 4).

Modal/hotspot branch (modal Sol author, root audit): FiniteMixedTraces 13
(repaired; finite incoming trace bridge), FiniteMixedFlux 3 (sphere-pairing
limit 4 pi squared), FiniteMixedInwardFlux 3 (literal inward Poynting integral
of the incoming half-fields tends to 2 pi squared times the amplitude energy,
positive for nonzero coefficients), FiniteMixedHerglotz 11 (EXACT identity:
`FiniteAngularHerglotz.incident k c` equals the finite mixed regular Debye field
evaluated at k times the point, no constant, no conjugation),
FiniteMixedScaledFlux 14 (1/k^2 power scaling derived; `normalizeK k c` has
unit limiting inward half-field power at frequency k), SimplePoleResidueForm 2
(abstract rank-one residue form), AxisymmetricPlaneMaximizer 7 (geometry only).
Scope note for the three remaining modal closure items:
`reviews/modal_closure_scope_2026_10_24.md` (smallest missing theorems:
`weighted_mode_in_volume_kernel`, which needs a complex-frequency radiation
representation; Hermite–Lindemann, absent from Mathlib; the modal continuation
and rounding assembly).

Fixed-angular branch (fredholm Sol author, root audit): ConicalFixedAngularInput 3
(final object emitted), ConicalFixedInputTransfer 8 (one fixed finite angular
input, chosen per small positive frequency BEFORE the rounding level, radius,
coordinate and threshold, gives eventually positive-measure superlevel sets of
the rounded total field at every threshold), ConicalNormalizedInputTransfer 6
(the same with the input replaced by its unit-limiting-inward-power
normalization), ConicalNormalizedInputHCurl 2 (regional H(curl) representatives
and weak Maxwell for the rounded fields), ConicalNormalizedInputCoefficient 5
(nonzero singular coefficient and projected-graph identity for the normalized
input, by uniqueness of the coefficient under scaling; the gauge system is
affine in the incident, so scaling is transferred by uniqueness, not by scaling
the system). The input still depends on k; it is not uniform in k. "Normalized"
means the limit of the inward half-field Poynting integral equals one; it is not
finite-radius power and not total-field power. No plane-maximum claim.

Channel branch (channel Sol author, root audit): RestrictedTEDatumLinear 4
(repaired), MaterialSourceLinear 2, RestrictedTEPolarization 4 (complex
polarization), RestrictedTETotalLinear 44, whose endpoint
`uniform_actual_inverse_to_dipoles` gives, for every tolerance and every fixed
finite index set, eventual integrability and an L1 whole-plane error bound
uniform over all coefficient vectors supported in that set with coordinates of
modulus at most one, under the same geometric hypotheses as the frozen
fixed-input theorem. This is still the explicit parity-device endpoint: the
named even-m basis identification, physical frequency/Poynting normalization,
finite physical background lift, counted-channel construction and the
finite-shell identification remain. Scope note requested:
`reviews/channel_closure_scope_2026_10_24.md` (in progress at the time of writing).

Root (Astra) source/inclusion branch (modal Sol audits): SourcePairedInverse 8
(inverse stability: norm-convergent operators with a unit limit difference have
eventually units, convergent inverses and convergent solutions; specialized to
the clamped paired-core operators), SourceCoreOperator 8 (material operators
depend only on kernel values on carrier x carrier; the clamped paired-core
operator eventually equals any operator carrying the literal shell tensor on an
inclusion support inside the core, with the weighted volume-integral form of its
components), ShellInclusionAlgebra 18 (ring algebra: push-through inverses,
shell Green element identities, the effective identity
`(1 - Si G Si)(Si T S) = (Si G S)(1 - S T S)` and the explicit two-sided inverse
of the combined block), ShellInclusionBlocks 3, ShellInclusionVolume 12 (the
dynamic volume block IS `1 - S c * kernel k R * S c` with the coefficient-
independent kernel `DynamicConvolution.operator k (2R) - physicalProjection`;
coefficient sum with pointwise disjoint supports; sqrt-multiplier additivity and
orthogonality; the combined shell-plus-inclusion block reduces exactly to the
shell block and the effective inclusion block, with explicit inverse and
solution formula). Author-final, independent audits requested:
ShellInclusionReaction 3 (effective block = inclusion volume block minus the
inclusion-weighted reaction operator `Si T Ss r Ss T Si`), ShellInclusionSmall 8
(norm bounds; smallness := errorBound ci + ci.bound * ‖scatteredGreen‖ < 1
makes the effective block a unit with explicit inverse bound, hence the combined
block is a unit whenever the shell block is). Fredholm Sol, root audit:
SeparatedScatteredRepresentation 7 (off-support a.e. pointwise dyadic
representation of the scattered field and of `kernel k R (S ci u)` on the
enclosing ball).

## Immediate next work (in order)

1. Kernel identification (requested from fredholm Sol as
   `ShellReactionIdentification`): identify root's reaction operator with the
   bounded material operator of the literal shell reaction tensor on the
   inclusion support, via the Bochner-integral form of `S cs (kernel (S ci u))`
   (weak identity through inner products and Fubini), commutation of the shell
   inverse and of `CoreMaterialEvaluation.evaluation` with the integral, and
   `SeparatedScatteredRepresentation.kernel_weighted_exterior_ae`.
2. Then assemble the full finite-shell-plus-inclusion reduction: with the
   identification, `SourceCoreOperator.eventually_operator_eq` shows the
   clamped paired-core operator equals the reaction operator of the paired
   shell for large shell index on the inclusion support, `SourcePairedCore.
   operator_limit` and `SourcePairedInverse` give convergence of the effective
   inverses and solutions to the central-inversion limit, and `ShellInclusionSmall`
   gives unit-ness for small inclusions. Record each step; no step is done yet.
3. Physical source symmetry (central inversion versus wall reflection: equal
   only in the proper-half-turn-invariant source sector, `HalfTurnReactionBridge`)
   and the remote annulus whole-plane return flux remain open after that.
4. Channel: discharge the scope note's smallest item; eventually tie the
   parity-device endpoint to the finite-shell reduction.
5. Modal: the smallest missing theorems are deep (see the scope note); do not
   claim modal closure. Hotspot: the fixed input is per-frequency; no uniform-in-k
   statement exists.

## Handoffs and how to resume safely

Agent handoffs from the October 23 stop remain valid historical records:
`reviews/modal_checkpoint_2026_10_23_stop.md`,
`reviews/fredholm_sol_stop_oct23_fixed_angular.md` (+ JSON),
`reviews/continuation_uniform_stop_2026_10_23.md`. Today's per-module author
reviews and independent receipts are under `reviews/` with the module's
snake-case name; scope notes are `reviews/*_scope_2026_10_24.md`.

Process that worked today: Sonnet ("6.1 Sol") subagents author and repair
drafts, one Lean process each; root (Astra) keeps the critical mathematics,
audits everything from source with fresh compiles, records receipts with
`tmp/record_after_5238.py` (root audits, logs `lean/logs/<M>-root-audit.log`)
or `tmp/record_modal_after_5238.py` (non-root audits of root modules, logs
`lean/logs/<M>-modal-audit.log` and receipt `reviews/<m>_independent.md`), and
alone touches Git. Never rerun the one-time `integrate_current_audits.py 5238`
or older checkpoint/release creators. Git checkpoints today: `f2cb699`
(stage 1), `b6f653b` (stage 2), `f37b0b4` (stage 3), plus later stage commits;
`tmp/` and `*.log` are gitignored, so evidence is copied under the checkpoint
folder and added with `git add -f`. Never stage `sites/`.

Workspace: D:/oq14. Compile with cwd D:/oq14/lean using
D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe
(`lake.exe env lean <Module>.lean` for a check, `-o .lake/build/lib/lean/<Module>.olean`
for the final object). Always run inside `( cd /d/oq14/lean || exit 9; ... )`:
the Bash tool's working directory drifts between calls and a compile started
from the wrong directory fails to find the project search path. The aggregate
`Mathlib` module is not built; import specific Mathlib files. Lean 4.19.0;
mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; nine pins. Small modules
compile in 10–60 s. Never clean root lean/.lake/build; never compile a
dependent before its dependency has a passing final object; use explicit UTF-8
reads (logs may have UTF-16 BOM). Memory is tight on the machine (commit charge
near its limit); keep concurrent Lean processes to about three.

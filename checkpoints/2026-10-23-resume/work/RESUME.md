# OQ14 paused checkpoint — October 23, 2026

**STOPPED at the user's explicit request: “stop and create checkpoint”.**
Do not resume proof work until the user asks. Full OQ14 closure and complete
Maxwell Lean formalization are unfinished. The latest checkpoint is
`checkpoints/2026-10-23-resume/`; read its manifest and the handoffs below.

## Exact verification boundary

The last clean combined release remains `oq14-maxwell-foundations-5238`,
commit `8a4a8bf4abb15d7ae6f2fc0fa4d63758c3c04248`: 5238 proof reports,
627 modules, 599 libraries, nine pinned dependencies, all15 diagnostic groups
passed, 113-page PDF. Its clean build has fourteen legacy tactic warnings,
exactly matching release4391, and no new warnings or errors.
The preserved delivery is `output/checkpoints/oq14-maxwell-foundations-5238/`.
PDF SHA256: `611c64b2041ace2988d2db781246a4a7dfb0a05c867c28ad09948ceb7b3b649d`.
Delivery ZIP SHA256: `ba907a88acbb9f69821d96adef7b35f4d0a80e30322454812debee14832db1c7`.

Beyond that release, the incremental ledger `tmp/audited_after_5238.json`
records169 independently reviewed and freshly checked modules /832 reports.
Every recorded report uses only propext, Classical.choice and Quot.sound.
These targeted checks are NOT a new combined clean aggregate release.
There are180 new Lean sources in the checkpoint: the manifest distinguishes
all169 independently checked modules from the eleven newer files. Some newer
files have author-only checks; others are unfinished. Compiler recovery output
and an old object file are never evidence that a current source passes.

## Completed root stage and immediate next work

The actual TM and TE finite physical material inverses, polarizations and
pointwise core Green integrals are proved, including origins and interfaces.
Their complete infinite angular-mode sum now equals the actual tensor response.
`SourcePairedTensor.uniform_actual_jet_limit` proves compact uniform convergence
of every fixed finite joint derivative for actual finite paired dielectric shells.
Author stages are frozen in the three `reviews/source_*_stage_2026_10_23.json`
files (Maxwell converse, physical modes, tensor limit); independent receipts are
in the incremental ledger.

The actual limit is central inversion. `HalfTurnReactionKernel` and
`HalfTurnReactionBridge` independently prove actual J covariance and equality
of central/wall volume integrals for integrable proper-half-turn-invariant
sources. This does not establish invariance of the material-inverse source.

`CompactCoreKernel` (7 reports, check2) and `SourcePairedCore` (5 reports,
check2) have clean author checks and objects, but independent audits were not
started before stopping. They extend compact kernels continuously by radial
clamping and derive convergence in the actual bounded material operator norm.
The entries eventually equal the literal shell tensor on the fixed core.
Next: independently audit these files, prove the actual weighted volume-integral
identity on the inclusion support, derive inverse stability and the full
finite-shell-plus-inclusion reduction. Then prove physical source symmetry
and control the remote annulus's complete whole-plane return flux.
No CompactCoreOperator or inverse-stability successor was written before stop.

## Channel branch

Actual finite even-degree TE fields have prescribed edge jets and physically
orthonormal incoming channels, with common finite band and Gram completion.
Magnetic decay, the coherent whole-plane bound and the full four-term parity
flux budget are proved. `RestrictedTEDipoleLimit` independently proves the
actual explicit-parity inverse's complete whole-plane L1 limit to literal
polarized finite-ball dipoles, for each fixed actual input.

The next step is uniformity over all unit coefficient vectors in one finite
input space, using genuine operator linearity and finite polarization identities.
RestrictedTEFieldLinear has a clean four-report target check and object, awaiting
independent review. RestrictedTEDatumLinear failed its target check and
MaterialSourceLinear remains uncompiled. The channel handoff records exact
resume steps. Do not replace fixed-input convergence with an assumed uniform bound.
The finite physical background lift, complete outgoing power/frequency bridge,
final counted-channel construction and named even-m basis identification remain.
The target has delta > eta > 0, arbitrary finite N, fixed frequency/common
positive dielectric bounds/square, unrestricted finite device support, and the
complete scattering output. Do not claim delta <= eta or a uniform support bound.

## Fixed-input hotspot and modal branches

Actual smooth angular caps approximate a finite directional input on a compact
ball. Genuine transverse harmonic L2 approximation then gives finite angular
Herglotz inputs with uniformly controlled electric-field error. Actual entire
Maxwell gauge and conical coefficient stability are proved.
`ConicalFixedAngularInput` passed its three-report target check2, but no final
object was emitted. It selects a nonzero finite angular input with retained
coefficient before rounding/threshold. It does not yet prove unit physical power.

`FiniteMixedFields` (13 reports) and `SphereVectorPairing` (5 reports) have clean
author checks/objects, awaiting independent root review. `FiniteMixedTraces`
is unfinished: check3 exited1, with one amplitude_apply elaboration error and
one unnecessary-tactic warning; no object. The next work is the actual finite
field-to-trace-map bridge, literal incoming flux limit, negative-phase Herglotz
field equality and positive-frequency scaling. Then normalize one fixed input
and transfer it through rounding without reselecting it for each threshold.

Full modal closure also still needs actual reciprocal-residue normalization,
infinite-degree pole isolation and simultaneous genuine three-dimensional
maxima in the prescribed plane. The target uses arbitrarily high Q, fixed real
pole frequency, common bounds and N-dependent insertion contrast. Driven field
peaks or angular energy alone do not establish that modal statement.

## Handoffs and safe resumption

Read the exact agent handoffs under reviews:
- `modal_checkpoint_2026_10_23_stop.md`
- `fredholm_sol_stop_oct23_fixed_angular.md` and its JSON
- `continuation_uniform_stop_2026_10_23.md`.

Use6.1 Sol subagents when the user resumes; retain root/Astra for critical
mathematics and integration. Root alone edits shared registries, release docs
and Git. Verify hashes before recording a proof. Use `record_after_5238.py` and
`record_modal_after_5238.py` only for new completed audits. Never rerun the
one-time `integrate_current_audits.py 5238` or older checkpoint/release creators.
No clean release regeneration, publication or new theorem stage was started
after the stop request. Old releases and checkpoints remain preserved.

Workspace: D:/oq14, PowerShell. Compile with cwd D:/oq14/lean using
D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe.
Lean4.19.0; mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; nine pins.
Python: C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe.
Use explicit UTF8 source reads; logs may have UTF16 BOM. Never clean root
lean/.lake/build; never compile a dependent before its new dependency passes.
Never touch, stage or package the unrelated sites/ tree.
The Downloads manual was absent at the last recorded comparison; original
scope evidence is in reviews/original_scope_2026_10_20.md, not a fresh comparison.

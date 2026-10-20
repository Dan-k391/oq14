# OQ14 resume checkpoint — October 20, 2026

**ACTIVE: the user explicitly resumed after the October20 checkpoint.**
The immutable pause snapshot remains in `checkpoints/2026-10-20-resume/`.
The complete Maxwell Lean task remains unfinished.
The user's model preference is 6.1 Sol for subagents and Astra for important proof
design, integration and audits.

## Current active work

The checkpoint's pending final independent weak-continuation check and the
seven volume-adapter proofs are now finished and audited. The new registered
batch has **2183 selected declarations / 198 modules / 170 libraries**.
All150 additions passed targeted compilation and full-source review.
Its new clean aggregate and PDF/package checks are pending. See
`reviews/interior_continuation_2183.md` for the exact frozen sources.

Root/Astra owns proof design, audits, shared registration, clean aggregate
and packaging. The 6.1 Sol agents work on distinct files:

- fredholm_sol: `RadialMaterialCells.lean`, actual sphere/annulus/exterior
  connectedness and interface bridge geometry.
- continuation_review_sol: `FiniteRadialPartition.lean`, actual finite
  ordered-radius cover, reachability and partition construction.
- modal_sol: `PiecewiseScattering.lean`, actual physical scattering
  assembly and radiation from the proved geometric-partition inverse.

These active new files are outside2183 until they are compiled and reviewed.
Unrelated user-created `sites/` is untracked and must remain untouched.
Do not clean the root Lean build while agents are active. Use the independent
checkout for the aggregate.

The paused snapshot remains immutable at tag `oq14-resume-2026-10-20`, commit
4216802265d44d891e996af05ba632aa9d400d67. Its archive SHA256 is
ab0399142662af5d88c737f261929bf0b9f9878b7d9ba2e70051088fd39e6365.

## Verification and release state

The **2033-declaration clean aggregate PASSED** at exact commit
`cef17ae243efd453c425ca903846e22629af1691`, with 176 registered modules / 148 libraries.
The root build was cleaned; all nine dependency revisions match their pins;
only propext, Classical.choice and Quot.sound appear in selected dependencies.
All 15 diagnostic groups also passed at that clean commit.
Proof and diagnostic evidence is preserved in
`output/checkpoints/proof-build-2033/` and in this resume checkpoint's evidence.
Its PDF check failed on one 31.24463pt overfull paragraph (verification.tex
lines 566–582). The working source now adds internal allowbreak points to
FiniteMeromorphicInverse, MeromorphicOperator and AnalyticCompactInverse.
**That layout fix has not been rebuilt. No 2033 PDF/package is claimed.**

The latest coherent packaged release remains `oq14-maxwell-foundations-1660`,
commit `f7e03a7db06c084abb1279e0affef93d3a72082c`: clean aggregate 1660,
15 diagnostics, 108-page visually checked PDF, no unresolved references or
overfull boxes. Matching artifacts are in
`output/checkpoints/oq14-maxwell-foundations-1660/` and top-level output.

- Delivery SHA256: `31190f182f399636e9f1bcbbcf6522ec4dba05191924cb685bf48dc8bb41b777`
- PDF SHA256: `2292c6663c7da4813c4321154d078c7bd258d71f7c408cb684bee63db43f0543`

The 1835 clean aggregate also passed at
`44ca66d9d6db10e555ae1881bdc1399aefb88100`, but its PDF failed and it was
not packaged. Evidence remains in `output/checkpoints/proof-build-1835/`.
Earlier releases and the October18 checkpoint are preserved.

## Newly registered proof sources

The17 sources/120 reports saved at the pause are now registered, together
with the finalized seven volume-adapter proofs and23 additional reports in
RegionalMaxwellContinuation, MaterialCellGraph, PiecewiseMaxwellUniqueness
and MaxwellZeroField. The complete inventory and scope are in
`lean/README.md` and `reviews/interior_continuation_2183.md`.

## Mathematical design to continue

Exterior Maxwell Rellich is now fully derived for actual homogeneous volume
fields: both fields vanish outside the material support at positive real
frequency, without support smallness. This does not yet prove global zero.

The interior scalar argument is now proved without assuming solution
analyticity or an unproved regularity theorem. Genuine compact annular tests,
polar integration and homogeneous harmonic polynomials give the radial moment
equation. Actual derivatives and the one-dimensional fundamental lemma give
the classical flux ODE. Finite-interval Hankel uniqueness and harmonic density
give smooth ball continuation. Literal translations and connectedness give
smooth domain continuation.

For weak fields, actual compact normalized mollifiers solve the classical
equation eventually on every fixed inner ball. They inherit a zero germ from
an AE-zero neighborhood. Smooth continuation makes the mollified values
eventually zero; genuine AE convergence gives zero for the original weak
field. A countable open subcover globalizes the AE germs. Full weak-to-smooth
representative regularity is not needed for this uniqueness argument and
has not been claimed.

Completed interface step: let U,V be connected open material cells, and B an open connected set
covered almost everywhere by U union V, meeting each in a nonempty open set.
If E is AE zero on U and epsilon=epsilonV on V, then epsilon*E=epsilonV*E
AE on B. `RegionalMaxwellLocalization` derives the actual constant-material
weak scalar Helmholtz equation there. `WeakHelmholtzContinuation` propagates
zero across B, then throughout V. Electric vanishing alone suffices for the
volume uniqueness adapter; no initial magnetic zero premise is required.

Completed: `MaterialCellGraph.lean` and `PiecewiseMaxwellUniqueness.lean` use actual bridges
with AE two-cell coverage and nonempty overlaps, geometric reachability
(`Relation.ReflTransGen`), and an AE cover of space by material cells.
The actual PDE propagation is discharged in the global uniqueness theorem.
Concrete geometry instances for the finite constructions are now being proved.

Further gaps: concrete material geometry and physical scattering assembly; all-angular-order
Green convergence and whole-plane flux; conical coefficients, Runge and
rounding; physical reciprocal mode normalization and infinite-degree modal
isolation; complete channel and hotspot constructions. Do not replace any
missing proof with its conclusion as a hypothesis or a custom axiom.

## Written scientific scope

The written unrestricted fixed-section channel finiteness assertion is
disproved for each fixed delta>eta>0, with the full scattering map as output,
common ordinary positive material bounds and frequency, and unrestricted
finite support. Stronger bypass thresholds, receiving outputs and uniformly
bounded support remain separate questions.

The written modal hotspot theorem constructs one genuinely normalized high-Q
mode with arbitrary finite peak count, fixed real frequency, common ordinary
bounds and actual maxima in the prescribed plane patch. Contrast may depend
on N within those bounds. Do not silently broaden these quantifiers.

## Reproduction and operational notes

Workspace `D:/oq14`; PowerShell. Pinned runtime:

- Python `C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`
- Lake `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`
- Tectonic `D:/oq14/.tools/tectonic/tectonic.exe`
- Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; nine locked dependencies.

Targeted checks from `lean/`: `lake env lean File.lean`; add
`-o .lake/build/lib/lean/File.olean` for importable objects.
Never clean the root Lean build while agents are active. Aggregate only in
`tmp/clean-checkout`, whose root build is independent and dependency junction
reuses pinned packages. It remains at `cef17ae243efd453c425ca903846e22629af1691` with a passed build.

After a frozen batch is committed, update that checkout to the exact commit,
then run `lean/build.py --lake <path> --log-dir output/lean`,
`scripts/verify.py`, and `scripts/build.py --cached --tectonic <path>`.
Set `TECTONIC_CACHE_DIR=D:/oq14/tmp/tectonic-cache`, use Python `-X utf8`.
Inspect changed PDF pages before packaging with `scripts/package_release.py`.
Only copy coherent release artifacts together. No repository was published.

Executed one-time scripts in tmp include integrate_1058.py, integrate_1312.py,
integrate_1660.py, integrate_1835.py, integrate_2033.py,
create_annular_equation.py, preserve_1058.py, preserve_1312.py,
preserve_1660.py, create_stop_checkpoint_20261020.py and integrate_2183.py. Do not rerun them.
No source or dependency upgrade is authorized by routine resumption.

Original-scope audit: `reviews/original_scope_2026_10_20.md`. The original
manual is currently unavailable; cached tutorial and manuscript quantifiers
were compared. Do not label every OQ14 interpretation closed. The exact
channel regime and modal normalization must remain explicit.

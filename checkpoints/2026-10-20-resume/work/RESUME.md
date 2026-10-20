# OQ14 resume checkpoint — October 20, 2026

**PAUSED at the user's explicit request: "ok, stop here create checkpoint for later resume".**
No proof work, compiler job, subagent task, or automation remains running.
Resume only when the user asks. The complete Maxwell Lean task remains unfinished.
The user's model preference is 6.1 Sol for subagents and Astra for important proof
design, integration and audits.

## Start here on resumption

1. Read this file and `checkpoints/2026-10-20-resume/manifest.json`.
   The checkpoint saves exact working bytes, including unfinished work.
2. Independently recompile the final `WeakHelmholtzContinuation.lean`. Root's
   final compile and object generation passed with all four standard-only reports.
   The independent agent reviewed the full mathematics, but its last compiler
   run preceded the final `he.mono (fun _ hn => hn.symm)` syntax fix. Do not
   confuse that old failed run with the final root PASS.
3. Finalize `HomogeneousVolumeUniqueness.lean`: its seven proofs compile, but
   it has no dependency prints, no emitted object, and no completed independent
   source audit/review. Add the seven prints, check the object, audit and freeze.
4. Prove actual material-interface continuation by composing regional Maxwell
   localization with the now-proved weak Helmholtz continuation. Then prove
   the required material-cell geometry and global homogeneous uniqueness.
5. Register only the finished audited modules as a new batch. Update the
   formal coverage ledgers, commit it, and run a clean aggregate in the
   independent checkout. The new modules listed below are NOT registered yet.
   Finish PDF layout verification before making a new coherent release.

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

## New, unregistered proof sources

There are 17 sources with 120 selected declarations that passed targeted
compilation and complete-source mathematical review, plus the seven-theorem
compiling volume-adapter draft. These targeted checks do not constitute a
new clean aggregate or a completed formalization.

| Module | Reports | Actual result |
|---|---:|---|
| AnnularMoment | 15 | Literal spherical moment first/second derivatives on finite annuli |
| AnnularMomentClassical | 2 | Actual weak annular moments imply classical residual/flux |
| AnnularMomentEquation | 3 | Actual spatial Helmholtz equation gives weak radial tests |
| RadialIntervalUniqueness | 5 | Finite-interval Hankel ODE uniqueness from zero data |
| RadialIntervalFlux | 4 | Actual radial flux uniqueness from a zero neighborhood |
| HelmholtzBallContinuation | 4 | Actual smooth Helmholtz zero germ implies whole-ball zero |
| HelmholtzTranslation | 11 | Literal translated derivatives, Laplacian and ball equations |
| LocalZeroPropagation | 4 | Topological propagation of a supplied ball property |
| HelmholtzUniqueContinuation | 3 | Actual smooth Helmholtz continuation on connected open sets |
| LocalHelmholtzRepresentation | 10 | Genuine compact/local Green representation |
| WeakHelmholtzRegularity | 7 | Actual convolution derivatives and reduced-ball classical PDE |
| HelmholtzMollifiers | 5 | Actual bump support, eventual PDE, and AE convergence |
| HelmholtzMollifierZero | 5 | Actual AE-zero neighborhoods force mollifier zero germs |
| LocalAEZeroPropagation | 6 | AE-germ propagation and genuine countable-cover globalization |
| WeakHelmholtzContinuation | 4 | Actual weak Helmholtz continuation on connected open sets |
| RegionalMaxwellHelmholtz | 22 | Actual regional Maxwell tests imply Gauss and scalar Helmholtz |
| RegionalMaxwellLocalization | 10 | Actual global variable-material tests localize across interfaces |
| HomogeneousVolumeUniqueness | 0 (draft) | Seven compiling proofs: local integrability and electric AE zero imply volume unknown zero |

Root independently compiled and read the two RegionalMaxwell sources, the
translation, AE topology, smoothing, and zero-inheritance sources. Earlier
annular/ODE sources were also independently checked. Root ball and smooth
continuation sources received independent source and compiler PASS.
Weak continuation has root compiler PASS and independent source PASS, with
the final independent compiler rerun outstanding as stated above.
Hashes and per-file status are in the checkpoint manifest.

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

Next interface step: let U,V be connected open material cells, and B a ball
covered almost everywhere by U union V, meeting each in a nonempty open set.
If E is AE zero on U and epsilon=epsilonV on V, then epsilon*E=epsilonV*E
AE on B. `RegionalMaxwellLocalization` derives the actual constant-material
weak scalar Helmholtz equation there. `WeakHelmholtzContinuation` propagates
zero across B, then throughout V. Electric vanishing alone suffices for the
volume uniqueness adapter; no initial magnetic zero premise is required.

Planned but NOT STARTED: `MaterialCellGraph.lean`. Use actual bridge balls
with AE two-cell coverage and nonempty overlaps, geometric reachability
(`Relation.ReflTransGen`), and an AE cover of space by material cells.
Prove actual geometric instances for the finite construction, not an assumed
PDE continuation conclusion. The abstract reachable-property induction alone
does not close global Maxwell uniqueness.

Further gaps: arbitrary-support global uniqueness/solvability; all-angular-order
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
preserve_1660.py and create_stop_checkpoint_20261020.py. Do not rerun them.
No source or dependency upgrade is authorized by routine resumption.

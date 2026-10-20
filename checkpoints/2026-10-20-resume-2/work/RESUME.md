# OQ14 resume checkpoint — October 20, 2026 (second pause)

**PAUSED at the user's explicit request: "create checkpoint and stop".**
All three 6.1 Sol agents stopped and reported no active compiler sessions.
Root stopped the unfinished clean aggregate (session93252, interrupted exit1).
No proof work or automation should resume until the user asks.
The complete requested Maxwell formalization remains unfinished.

## Start here

Read `checkpoints/2026-10-20-resume-2/manifest.json` and its exact snapshots.
The active working files remain in place. Never restore over later work.
The user's model preference remains 6.1 Sol for subagents, Astra for
important proof design, integration and audits.

1. Finish independent source/compiler audits of `HankelIntermediateBounds`
   (6), `CavityBallBridges` (3), `ShellInclusionCells` (6), and
   `DisjointBallPartition` (2). Author/root targeted compilation and object
   generation passed for all four. The other ten new finished modules
   already have independent full-source and compiler PASS. Write the missing
   review for the independently passed `HankelCoefficientBounds` (16).
2. Repair the two preserved drafts, retaining their genuine mathematics:
   `CapLegendreSeries` has four chain-rule failures; `PlaneSourceKernel`
   has three subtraction-expression rewrite failures. Neither is compiled
   or registered. Exact errors and subsequent steps are below.
3. Register only finished, audited sources. The 14 compiled new sources
   contain156 selected declarations, all outside the current2234 registry.
   Do not accidentally include the two unfinished sources in an aggregate.
4. The independent checkout `tmp/clean-checkout` remains at `cc29d768fb89b308bd87d7d926fdc5122c505cfa`.
   Its2234 aggregate was interrupted at the user's stop request. Rerun a
   genuinely clean aggregate there after freezing the desired source commit.
   Never clean the root Lean build while agents are active.

## Current verification and release state

Registered source commit: `cc29d768fb89b308bd87d7d926fdc5122c505cfa`.
**2234 declarations /203 modules /175 libraries.** Its new201 declarations
since2033 passed targeted checks and full-source audits; the clean aggregate
is NOT certified. The stopped rebuild created many objects, but that is not
a full success. The old files currently under `tmp/clean-checkout/output/lean/`
are stale2033 evidence (provenance identifies cef17ae), not2234 evidence.

At exact clean2234 commit all15 diagnostic groups passed. Its110-page PDF
also passed references, citations and overfull-box checks, and pages105,
106 and108 were rendered and inspected. PDF SHA256:
`54fbadcb829da654c3bf1598314f238fa36b3c4eeef6283109aa6426446a049a`.
These PDF/diagnostic artifacts are preserved in this checkpoint's evidence.
There is no2234 coherent proof/PDF release package.

The last completed clean proof aggregate remains2033 at
`cef17ae243efd453c425ca903846e22629af1691`, with15 diagnostics.
The last coherent packaged release remains `oq14-maxwell-foundations-1660`
at `f7e03a7db06c084abb1279e0affef93d3a72082c` (108-page PDF).
Its delivery SHA256 is
`31190f182f399636e9f1bcbbcf6522ec4dba05191924cb685bf48dc8bb41b777`.
The earlier checkpoint tag `oq14-resume-2026-10-20` and all release evidence
remain preserved. This is a resume checkpoint, not a completion claim.

## Completed since the prior pause

Registered2183 established actual weak Helmholtz continuation, variable
Maxwell localization, actual interface continuation, geometric-cell global
uniqueness and the Fredholm inverse. Registered2234 constructed all geometry
for arbitrary finite concentric positive-material layers, actual physical
scattering fields, and analytic volume inverses near every positive real
frequency. Geometry and PDE propagation are proved, not supplied as the
missing conclusion. Arbitrary outgoing PDE-to-volume equivalence remains
outside the formal coverage.

The new unregistered modules prove actual angular-measure symmetry and the
cap-weighted coordinate Rayleigh trial below2; actual all-degree Hankel
energy and low-order bounds, real basis/Wronskian and intermediate-range
factorial/exponential estimates; actual connectivity and bridges for
separated balls and an enclosing cavity/single shell; and inverse-cube
actual Maxwell plane-flux tails with genuine2D integrability, including
cross terms. They do not yet prove full Green convergence or either final
device theorem. Per-module hashes, reports and audit status are in manifest.

## Exact unfinished proof steps

`CapLegendreSeries.lean`: latest compilation EXIT1, no object and no prints.
Four failing proofs are `pole_hasDerivAt`, `poleD_hasDerivAt`,
`odd_hasDerivAt`, `oddD_hasDerivAt`: invalid named argument `g` for
`HasDerivAt.comp` and inference for the odd z-squared composition. Fix with
explicitly typed inner derivatives and actual binder names. Generic
power-series summability/differentiation, moment recurrences and the
Legendre algebra produced no further errors, but the complete source has
not passed. Then prove derivative-series parameter continuity, exact
Lambda0/2 endpoints and odd positivity. The intended actual shooting uses
P_Lambda regular at z1 and F_Lambda odd at z0. Matching determinant
D(Lambda)=(1+d)P'_Lambda(t)F_Lambda(t)-P_Lambda(t)F'_Lambda(t) has D0<0,
D2=d*t>0 for0<t<1,d>0. IVT gives Lambda in(0,2), then
lambda=(sqrt(1+4Lambda)-1)/2 in(0,1). This shooting theorem and the genuine
sphere weak/H1 lifting remain unproved. `CapAngularShooting.lean` not created.

`PlaneSourceKernel.lean`: latest compilation EXIT1, no object/no prints.
Errors around lines152,184,194 concern `integral_add` with a Pi subtraction
and `response_plane_sub` rewrite shapes. The actual compact source region,
positive plane gap, compact-product kernel bound and continuity elaborate;
do not call the full draft compiled. Next prove local disk E/H component
bounds from the actual compact kernel bound, combine with `MaxwellPlaneTail`
for a whole-plane bilinear L1 bound depending on k,R,gap, and prove actual
source subtraction and L1 convergence. `MaxwellPlaneL1.lean` not created.

Geometry next: `ShellInclusionCells` gives a literal single-shell partition
with inclusions/cavity/shell/exterior. After its independent audit, extend
to arbitrary finite radial shells by replacing cell0 of
`FiniteRadialPartition` with the proved cavity; use inclusion-to-cavity
bridges, a cavity-to-first-shell bridge and existing higher radial bridges.
No multishell source was started. Then instantiate the actual global
Maxwell uniqueness/scattering theorem for the final channel geometry.

Channel next: Hankel low and intermediate estimates are proved, but high
barrier positivity/regular-solution lower bounds, actual stack transfers,
all-order physical Green convergence, self-consistent inclusion responses,
coherent whole-plane flux convergence and counted-space power identities
still require formal construction. Do not replace them with hypotheses.
Modal gaps include conical eigenfunction/coefficient construction, Runge,
rounding, physical reciprocal normalization, infinite-degree isolation and
the final simultaneous peaks.

## Scientific scope and operational notes

The written channel disproof fixes delta>eta>0 with full scattering output,
common ordinary material bounds/frequency and unrestricted finite support.
Stronger bypass, receiving-hemisphere or uniformly bounded-support problems
remain separate. The written modal theorem concerns an actual normalized
high-Q QNM with maxima in the prescribed plane patch. Its reciprocal residue
normalization must remain explicit. See `reviews/original_scope_2026_10_20.md`;
the original Downloads manual is currently absent, so exact manual comparison
cannot be certified from its historical hash alone.

Workspace D:/oq14, PowerShell. Python:
`C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Lake `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`.
Tectonic `D:/oq14/.tools/tectonic/tectonic.exe`.
Lean4.19.0, mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, nine locked dependencies.
Use Python -X utf8 and TECTONIC_CACHE_DIR=D:/oq14/tmp/tectonic-cache.
Target: `lake env lean -o .lake/build/lib/lean/Module.olean Module.lean`.
Clean aggregate: `python lean/build.py --lake <path> --log-dir output/lean`
in the independent checkout. Diagnostics `python scripts/verify.py`; PDF
`python scripts/build.py --cached --tectonic <path>`. Only package artifacts
from one matching clean commit after all checks and visual inspection.

One-time scripts `integrate_1058.py`,1312,1660,1835,2033,2183,2234;
`create_stop_checkpoint_20261020.py`, `create_stop_checkpoint_20261020_2.py`,
the preserve scripts and create_annular_equation.py must not be rerun.
The unrelated untracked `sites/` belongs to the user and must remain untouched.
No external repository, site, or paper was published.

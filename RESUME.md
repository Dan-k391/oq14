# OQ14 resume checkpoint — October 20, 2026 (second pause)

**ACTIVE: the user explicitly resumed from the latest checkpoint.**
The immutable pause snapshot is `checkpoints/2026-10-20-resume-2/`.
Its 27 working files and 32 evidence files were verified before resumption.
The three 6.1 Sol agents are continuing the Legendre shooting, plane-source
L1, and finite-shell inclusion geometry proofs. Root owns audits,
important proof design, shared integration and the clean aggregate.
The previous clean aggregate (session93252) was interrupted at the pause;
it remains uncertified until a new genuinely clean build succeeds.
The complete requested Maxwell formalization remains unfinished.

## Current active integration

All156 completed declarations from checkpoint2 now passed independent
source/compiler audits and are registered: **2390 declarations /217 modules
/189 libraries**. See `reviews/angular_geometry_plane_2390.md`. The new clean
aggregate and coherent PDF/package remain pending. The latest completed
clean proof aggregate is2033; the latest coherent package is1660.

The immutable checkpoint `oq14-resume-2026-10-20-2` remains at
b04414fe1912c76f46dc394c61d3a4ac28687675. Its verified archive SHA256 is
6acc0433c8ffff277e0ca0950e2c3a65a521b83617624e9ee3f8ab0669813776.
It preserves27 working files and32 evidence files. Its pause status is
historical; the user has explicitly resumed.

Active6.1 Sol ownership: fredholm_sol repairs and extends CapLegendreSeries
and actual angular shooting; continuation_review_sol develops the literal
plane-source compact bounds and whole-plane L1 continuity; modal_sol builds
finite layered inclusion geometry and actual Maxwell scattering adapters.
Root owns proof design, independent audits and shared integration. Never
clean the root Lean build while agents are active. The independent checkout
was at cc29d768fb89b308bd87d7d926fdc5122c505cfa before this integration;
advance it to the exact new source commit before a genuinely clean build.

The2234 PDF110-page check and15 diagnostics passed; its full Lean build was
interrupted at pause. In particular its old output/lean files are2033
evidence, not a2234 success. Check exact provenance on every new artifact.

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

`tmp/integrate_2390.py` is also executed and non-idempotent; do not rerun it.

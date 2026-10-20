# Active OQ14 continuation — October 20, 2026

The user explicitly resumed the latest immutable checkpoint and requested
continued work toward full OQ14 closure and complete Lean proofs. Do not
pause or stop at this working status file without a new user request.
Use the existing 6.1 Sol agents; root owns important proof design, audits,
shared integration and exact-source verification.

## Current registered proof set

2595 declarations / 229 modules / 201 libraries. All newly registered
sources passed full-source and independent pinned-compiler audits. Reviews
`angular_geometry_plane_2390.md` and `actual_constructions_2595.md` give exact
scope. The complete requested Maxwell formalization remains unfinished.

Clean aggregate session 89998 is running in D:/oq14/tmp/clean-checkout at
2f1ca342b33687c154226129f8417487dad3a175 (2390 declarations). Its 15 diagnostics
and 110-page PDF passed, no unresolved references or overfull boxes. Pages
106 and109 were visually inspected. PDF SHA256:
b05d9298e67fe66d8b0ac863b9a66b9cc95843a82ddc0113a135d3e080a0f92c.
Do not advance that checkout until the running aggregate finishes. Existing
output/lean provenance may still be2033 until the new build succeeds.
The last completed clean aggregate is2033; last coherent package is1660.
Never clean the root Lean build while agents are active.

## Active mathematical work

Root has proved actual Hankel polynomial coefficient positivity and the
outgoing radial load sign in every degree. Those sources are independently
audited and now registered. New RadialLayer.lean constructs actual scaled
homogeneous fundamental matrices and determinant-one transfers, actual
solutions, initial matching and endpoint transfer formulas; its current
unregistered draft compiled once, before report emission. Root is extending
actual propagation and barrier estimates.

modal_sol owns actual all-degree regular Riccati–Bessel series identification
and barrier estimates. Raw ModalAlgebra.psi has Laurent default values at0;
identify the genuine regular series for nonzero arguments and use its
continuous extension for origin limits. No singular-origin uniqueness or
series identification may be assumed.

fredholm_sol completed the actual normalized one-dimensional cap weak
profile and independently audited root Hankel positivity. Next it is
investigating genuine spherical parametrization/coarea and arbitrary-test
lifting. No sphere weak equation or H1 result has been proved yet.

continuation_review_sol completed actual fixed-gap whole-plane L1
continuity and the actual dynamic support-volume estimate. It now owns
SphereReactionKernel.lean and BoundedMaterialKernel.lean for literal sphere
reaction kernels and an actual material-volume operator bound. Exact static
sphere polarization, self-consistent inclusion asymptotics and moving-gap
flux limits remain separate.

Remaining full constructions include actual finite-stack transfer estimates,
regular barrier lower bounds, all-order physical Green convergence,
self-consistent inclusion responses, common-stack coherent whole-plane flux,
counted-space power identities, sphere/conical Maxwell coefficient lifting,
Runge approximation, rounding, physical reciprocal normalization,
infinite-degree pole isolation and final simultaneous modal maxima.
Do not insert these conclusions as hypotheses or count them as closed.

## Immutable prior checkpoint

Tag oq14-resume-2026-10-20-2, commit
b04414fe1912c76f46dc394c61d3a4ac28687675; directory
checkpoints/2026-10-20-resume-2/. Archive SHA256
6acc0433c8ffff277e0ca0950e2c3a65a521b83617624e9ee3f8ab0669813776.
Its27 working files and32 evidence files were verified before this resumption.
Do not rerun its creation or working-byte-verification scripts now: live
work has advanced. The original checkpoint remains immutable.

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

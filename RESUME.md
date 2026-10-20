# Active OQ14 continuation — October 20, 2026

The user resumed work toward full OQ14 closure and complete Lean proofs.
Continue until completion or a new user stop request. Use the existing
6.1 Sol agents; root owns important proof design, audits and integration.
The complete requested Maxwell formalization remains unfinished.

## Registered sources and verified release

2804 declarations / 247 modules / 219 libraries, with full-source and
independent pinned-compiler audits for the new files. Exact scope is in
reviews/actual_constructions_2804.md. This revision needs a clean aggregate.

The 2390 milestone at 2f1ca342b33687c154226129f8417487dad3a175 passed a clean
aggregate, all 15 diagnostics, and the 110-page manuscript with no unresolved
references or overfull boxes. Rendered pages 106 and 109 were inspected.
PDF SHA256: b05d9298e67fe66d8b0ac863b9a66b9cc95843a82ddc0113a135d3e080a0f92c.
Local tag: oq14-maxwell-foundations-2390. Fourteen matching artifacts are
preserved in output/checkpoints/oq14-maxwell-foundations-2390/ and copied
to top-level output. Delivery: 5002464 bytes, SHA256
011b8e9ed5767c25d8ae5ecf1f14b8a25731fa7910a794dfdc74ff0320cacf4e.
This is the latest completed coherent release. No external publication.

Use D:/oq14/tmp/clean-checkout for clean aggregate work after checking its
exact revision and active sessions. Never clean the root Lean build while
agents are active. Old aggregate session 89998 finished EXIT0.

## Active mathematical ownership

Root completed actual layer solutions, shared-radius stack energy and load,
core source coefficients, scalar Green branch jump and barrier source bounds.
Next: physical radial gluing, actual common-stack limits, spatial Green
reconstruction and uniform all-order/whole-plane estimates.

modal_sol completed actual regular series, origin limits, barrier positivity
and logarithmic bounds. Next: sharp Gaussian regular lower bound via an
actual weighted Riccati deficit and integrating factor. Raw ModalAlgebra.psi
is not the continuous extension at zero.

fredholm_sol completed actual coordinates and the angular measure formula.
Next: arbitrary smooth-test lifting of the cap profile, integrable endpoint
slopes, actual sphere weak equation and H1.

continuation_review_sol completed actual explicit parity-kernel operators
and unique solutions. Next: exact ball Newton potential and C1 matching,
genuine weak Hessian/L2 projection identification and static polarization.

Remaining full constructions include all-order physical Green convergence,
self-consistent inclusion asymptotics, moving-gap coherent whole-plane flux,
counted-space power identities, conical Maxwell coefficient lifting, Runge,
rounding, physical reciprocal normalization, infinite-degree pole isolation
and final simultaneous modal maxima. Do not insert these conclusions as
hypotheses or count them as closed.

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

One-time integration scripts integrate_2595.py and integrate_2804.py were also executed; do not rerun.

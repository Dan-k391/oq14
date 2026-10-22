# Active OQ14 continuation — October 22, 2026

The user requested continuation toward full OQ14 closure and complete actual
Lean Maxwell proofs. Keep working until complete or an explicit user stop.
Existing 6.1 Sol agents own disjoint proof modules; root owns important proof
design, independent audits and integration. Full formalization is unfinished.

## Registered and packaged state

3404 reports /323 modules /295 libraries. All 242 new reports have complete
source and independent pinned-compiler audits, no warnings and only standard
foundations. See reviews/actual_constructions_3404.md. This newly registered
revision needs a genuine clean aggregate, updated PDF and diagnostics.
Do not run a root aggregate: agents' unregistered drafts share lean/.

Completed coherent release: oq14-maxwell-foundations-3162 at
9b2443c6e5718c8ef5c5b7e0de76520b0582f74d. Clean aggregate PASS, nine dependency
checks PASS, 15 diagnostics PASS, 111-page PDF PASS; pages 106/107/110/111
visually inspected. Fourteen matching artifacts are preserved in
output/checkpoints/oq14-maxwell-foundations-3162/ and at top-level output.
Delivery: 8202296 bytes; SHA256
030205700ea96317a1624dd1e01de09ceea47328acbc652a51ab14464ff79514.
PDF SHA256 f7be07a2734772f00ca4c1857c0f4826360716efabd4753b482e1cf290443086.
Older releases remain preserved. No external publication.

tmp/clean-checkout is the independent checkout; its 3162 aggregate session
28732 completed exit0. Confirm its exact revision before advancing. Never
clean the root Lean build while agents are active.

## Active proof tasks

Root: actual finite-stack coefficient limits, complete scalar mixed-
derivative convergence and local Debye Maxwell calculus are registered.
Current RadialQuotient and SphericalScalarWaves connect actual Riccati waves
to scalar PDE; then actual global regular and punctured outgoing TE/TM
Maxwell waves. Continue normalized angular basis/addition and spatial dyadic
Green reconstruction. Retain important positive-frequency cone proof design.

modal_sol: actual SolidRadialSeries21 and SolidScalarHelmholtz10 frozen beyond
registration, with real global regular scalar Helmholtz waves including the
origin. Root compiled the former independently. Current all-order actual
normalized radial derivatives and spatial bounds. Never infer full vector
Green closure from scalar convergence alone.

fredholm_sol: actual singular static conical field is registered, with weak
gradient/curl/div, local finite energy and open-cone blowup. Beyond registration:
ConicalComplexTests6 and ConicalHCurl4 frozen, requiring root audits. Current
actual radial inhomogeneous particular formula under continuous forcing,
bounded remainder and finite-energy exclusion. Genuine weighted Maxwell
estimate, positive-frequency correction and retained coefficient remain.

continuation_review_sol: actual finite-ball inverse/source errors and exact
Newton moments registered. New SphereReactionLipschitz5 and Dipole5 passed
root source/compile audits; FiniteSphereReaction5 and Scale3 await audit.
Current gain amplification and subsequent actual moving-gap plane estimates.
Finite physical-stack identification still requires spatial Green assembly.

Still essential: all-order spatial Green identification, moving-gap coherent
whole-plane flux and counted-space power identities, conical Maxwell lifting,
Runge, rounding, actual reciprocal modal normalization, infinite-degree pole
isolation and simultaneous modal maxima. Do not replace any desired
conclusion by a hypothesis.

## Immutable checkpoint and scope safeguards

The starting checkpoint checkpoints/2026-10-20-resume-3/ and its zip are
immutable: 23 work files/296 evidence files. Do not rerun working-file
equality now or restore it over later work. Tag oq14-resume-2026-10-20-3;
zip SHA256 7b808173455586f8bb16bac1ca4486c9ddd11740a346f11f71b50a0968a8d791.

Written channel scope: fixed delta>eta>0, complete scattering output, common
frequency/material bounds and unrestricted finite support. Stronger bypass,
receiving-only and uniform-support variants remain separate. Written modal
scope: actual reciprocal-residue-normalized high-Q QNMs, fixed real frequency
and common material bounds, actual 3D maxima in the plane patch, N-dependent
insertion contrast. The original Downloads manual was absent at the earlier
comparison: reviews/original_scope_2026_10_20.md. Do not claim exact current
comparison. Do not touch, stage or package unrelated sites/.

Runtime: .tools/lean/lean-4.19.0-windows/bin/lake.exe, pinned mathlib v4.19.
Python: C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe.
Tectonic: .tools/tectonic/tectonic.exe; cache tmp/tectonic-cache.
Integration scripts through integrate_3404.py are one-time mutations: do not
rerun. tmp/audited_batch_3404.json preserves exact frozen sources/logs.

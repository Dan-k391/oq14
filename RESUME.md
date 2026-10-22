# Active OQ14 continuation — October 22, 2026

The user requested continuation toward full OQ14 closure and complete actual
Lean Maxwell proofs. Keep working until complete or an explicit user stop.
Existing 6.1 Sol agents own disjoint proof modules; root owns important proof
design, independent audits and integration. Full formalization is unfinished.

## Registered and packaged state

4391 reports /469 modules /441 libraries registered. The 474 new reports have
complete-source and independent pinned-compiler audits, no warnings and only
standard foundations. See reviews/actual_constructions_4391.md and
tmp/audited_batch_4391.json. Matching clean aggregate/PDF are pending.
Do not run a root aggregate: agents' unregistered drafts share lean/.

Latest completed coherent release: oq14-maxwell-foundations-3917 at
e7d42ab2f86e8c23a992558bf5d89a42538c4347. All 3917 reports, nine dependency
checks and 15 diagnostics PASS; 112-page PDF visually checked. Fourteen
matching artifacts preserved in output/checkpoints/oq14-maxwell-foundations-3917/
and top-level output. Delivery 8885736 bytes, SHA256
1f29974477832b9c2b158dd2823ec02990821c5d5f54c284a7845a815be19747.
PDF SHA256 3ad0eff586c16beaa9a80a7e4f00c5d42ec0d8416d10845baf200218902d3338.
See reviews/clean_release_3917.md. The final bibliography item is alone on
page 112; improve that pagination in the next source revision.

Previous coherent release: oq14-maxwell-foundations-3404 at
155907f9137d85120d7e4fadbc0cf3cddd667d0c. Clean aggregate PASS, nine dependency
checks PASS, 15 diagnostics PASS, 111-page PDF PASS; pages 106/107/108/111
visually inspected. Fourteen matching artifacts are preserved in
output/checkpoints/oq14-maxwell-foundations-3404/ and at top-level output.
Delivery: 8456406 bytes; SHA256
c018deba6b6aebb578feba591a8253010a1f822ad1e3d10871ed6c19e4ead8f5.
PDF SHA256 455d3c5a2f81a2f5f3bcce107b73900235284509aa054bb483fb01227c12cd3b.
Older releases remain preserved. No external publication.

tmp/clean-checkout is the independent checkout at e7d42ab. Its 3917 aggregate
session 77633 completed exit0 and was consumed. The default legacy log output
was preserved in output/lean before restoring only those two generated log
paths. Both root and clone have the matching tag. Never clean the root Lean
build while agents are active. preserve_3917.py already executed; do not rerun
one-time integration or release scripts blindly.

## Active proof tasks

The 4391 registration adds actual normalized scalar Green coefficients and
angular L2 expansion, exact source jump/reduced sign, both weak Maxwell
equations through finite-chain interfaces in the layer annulus, actual smooth
weak-derivative representatives, the physical conical radial system and
finite-energy positive-power expansion, and actual whole-plane coherent
moving-gap error estimates for finite Maxwell parity illuminations.

Root owns independent audits, clean integration, full spatial layer
core/exterior assembly and major proof design. RadialMultiplierWeak3,
LayerMagneticProfiles6 and LayerMagneticMaxwell3 are frozen and independently
audited. Full source/exterior assembly remains; sourceState has a singular
core and must never be described as regular at the origin.

fredholm_sol: derive the actual annular L2 coefficient functional, positive
static normalization and positive-frequency retention from the actual radial
expansion. No nonzero coefficient or coefficient-continuity premise may be
substituted for the result. Runge and rounding follow.

modal_sol: actual scalar Green normalization and L2 expansion are checked.
Current imaginary-axis noncancellation and normalized spatial jet majorants
for actual derivative convergence. Dyadic k^3 normalization remains separate.

continuation_review_sol: actual finite-incident coherent whole-plane errors
are checked. Current literal incident amplitude/derivative estimates and
weighted forcing, then finite-point Gram coefficients and full channel
assembly. No assumed coherent-flux limit or source error.

Still essential: full spatial dyadic Green identification and source/layer
gluing, physical-stack/channel assembly, conical nonzero coefficient, Runge,
rounding, actual reciprocal modal normalization, infinite-degree pole
isolation and simultaneous modal maxima. Complete OQ14 Lean closure is not
claimed. Work remains active; no user stop was requested.

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
Integration scripts through integrate_4391.py are one-time mutations: do not
rerun. tmp/audited_batch_3404.json preserves exact frozen sources/logs.

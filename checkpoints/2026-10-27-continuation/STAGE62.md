# Stage 62 — proved transcendence and all-degree TM isolation

Date: October 28, 2026. Parent: `fcc38fc15ddb0409167ce4715624043e06cb5094`.
Work remains active; this is a rollback checkpoint.

The incremental ledger contains 424 independently audited modules / 3416
standard-only reports, adding 22 modules / 59 reports after stage 61. All
source/log hashes and qualified report lists were verified; the previous 402
records are unchanged. Targeted checks use existing dependency objects and
are not a clean aggregate rebuild.

The complete historical Lindemann–Weierstrass proof has been ported from
mathlib PR 28013 at commit d173f68c80a51efe617648e78fa1ae3e2b994a9d.
Five algebraic support ports and the full proof compile with only propext,
Classical.choice and Quot.sound. The rational Hermite–Lindemann endpoint
proves transcendence of exp(a) for every nonzero algebraic complex a.
There is no assumed transcendence premise. Source attribution and Apache-2.0
license are preserved, with historical sources and hashes under
evidence/lindemann-upstream. The pinned Lean and mathlib versions are unchanged.

`ModalTMIsolation` discharges the earlier algebraic obstruction. For algebraic
refractive index n outside 0, 1 and -1, every nonzero TM determinant zero is
simple and no distinct angular degrees share it. Every nonzero TM zero is
itself transcendental for algebraic n != 0. These are exact matching determinant
statements. General actual volume-kernel classification, selected-sector
one-dimensionality and the restricted inverse's simple rank-one residue remain.

Actual arbitrary volume L2 angular moments now agree with spherical-slice
inner products. Polar integration gives energy estimates and a bounded linear
physical angular-mode reconstruction operator, with an exact AE representative.
These results do not yet establish volume-operator commutation or classify
general Maxwell kernels. The ongoing weak radial analysis is outside this snapshot.

Smooth inward apex cap graphs and an inward bounded binary cone-ball corner
construction are checked. Positive corner partials, a negative radial derivative,
and quantitative apex/corner separation are proved. A full physical smooth-boundary
theorem, identification with the actual 3D coefficient, fixed-collar transmission
regularity and attained maxima remain in progress. The stage-61 one-input actual
simultaneous superlevel theorem remains valid for its common product-gate sequence.

Exact new source/log/exit bytes and ledger are preserved in
evidence/stage62-raw-evidence.zip. Metadata is in evidence/audit-metadata/stage62.json
and audited_after_5238-stage62.json. Frozen accepted source whitespace must not change.
The clean aggregate remains release 5238, commit
8a4a8bf4abb15d7ae6f2fc0fa4d63758c3c04248. Full OQ14 closure is unfinished.

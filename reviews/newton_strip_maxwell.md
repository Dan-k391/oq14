# Genuine electric and magnetic Maxwell representatives on a source-free strip

Frozen source: lean/NewtonStripMaxwell.lean.
SHA256: F0DE15D415D99880829092228D13E39332C7B62797FD32225849BABA2B6828F6.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/NewtonStripMaxwell-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

The actual static Hessian, dynamic remainder and gradient bounds give explicit
uniform kernel bounds at positive source-strip separation. Genuine source
integrability and these actual bounds supply uniform integrable dominators.
The literal dyadic electric and gradient magnetic convolution fields are
proved continuous on the actual strip abs(x_2)<d/2.

The actual existing FieldResponse.electric, containing the genuine L2 Newton
operator plus the actual dynamic remainder integral, is identified AE on this
open strip with the ordinary dyadic electric convolution. This uses the
previously derived actual Newton strip identity and genuine integral addition;
no exterior field identity or continuity conclusion is assumed.

Compact actual source support, integrable source coordinates, their actual
L2 representative identities, and actual positive source-height gap are
explicit. The magnetic field already has its literal gradient definition.
This covers the free Maxwell response, with a valid continuous representative
around the plane. It does not identify explicit parity reactions with a physical
finite-stack Green field, nor assert a moving-gap whole-plane flux limit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `f0de15d415d99880829092228d13e39332c7b62797fd32225849baba2b6828f6`. Independent log `lean/logs/NewtonStripMaxwell-root-audit.log`, SHA256 `b02167388bc55eab67b602627b5c7f627bc3ed92a635636d79fbe3e33ff127e7`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

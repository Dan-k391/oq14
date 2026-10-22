# Actual reflected sphere fields satisfy both Maxwell equations

Frozen source: lean/SphereParityMaxwell.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all five reports standard-only. Log: lean/logs/SphereParityMaxwell-final.log.
Independent audit pending.

The actual K moment derivative is composed with the genuine affine
reflection to derive all partials of magneticReaction. Cyclic reflection
signs and the actual curl K=-I*k*J identity prove
curl magneticReaction=-I*k*reaction. Combined with the independently
constructed first curl identity, the literal electric and magnetic parity
columns satisfy both actual vacuum Maxwell equations globally.

Actual Frechet differentiability of both parity fields is also derived
from the real sphere integrals and affine maps. No Maxwell, derivative,
reflection-curl or reconstruction conclusion is assumed. The results hold
at all points, including the source center, and all real frequencies.
Physical incoming-power normalization, finite incident Gram interpolation
and physical finite-stack Green identification remain separate work.
SHA256: 0030D3585500A01A0DFC9D08CAD3469CEB0C29B6E6FCC35CE93FDA36173C05F3

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `0030d3585500a01a0dfc9d08cad3469ceb0c29b6e6fcc35ce93fda36173c05f3`. Independent log `lean/logs/SphereParityMaxwell-root-audit.log`, SHA256 `bf28810723871267a477f762df7fef1b62fb09e7d5cfe30a4f82d8ca64fb584a`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

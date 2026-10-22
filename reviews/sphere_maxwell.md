# Genuine sphere-integral Maxwell pair

Frozen source: lean/SphereMaxwell.lean.
SHA256: 332C68907B6DAFC41982570FB0F1CC662C0CD807A39A32A95F5105BA8AF97625.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/SphereMaxwell-final.log.
Independent audit pending.

Actual dominated sphere-integral differentiation derives the K coordinate
partials. The actual unit-sphere norm gives the angular identity
(theta cross (theta cross e_j))_i = -amplitude(theta,i,j).
Integrability and genuine surface integral algebra then prove
curl K = -I*k*J. Combined with the previously derived curl J=I*k*K,
the literal globally defined J/K columns satisfy both genuine Euclidean
vacuum Maxwell curl equations with frequency k and unit epsilon/mu.

The identities hold at every spatial point and every real frequency,
including zero and the origin. No PDE, reconstruction or outgoing/incoming
identity is assumed in the proof. Reflected parity Maxwell membership,
physical incoming power normalization and finite-stack Green identification
remain separate constructions.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `332c68907b6dafc41982570fb0f1cc662c0cd807a39a32a95f5105ba8af97625`. Independent log `lean/logs/SphereMaxwell-root-audit.log`, SHA256 `71322c92fb5f957041347d5d75b81011d80e0f50b86b6457b86dd176fd3b5de1`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

# Genuine local plane inverse-power envelopes

Frozen source: lean/PlaneInverseLocal.lean.
SHA256: C5147D34607B31B856DDE051293846F422A84C383ED28328CB656748200FB405.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all seven reports standard-only. Log: lean/logs/PlaneInverseLocal-final.log.
Independent review is pending.

Actual positive-gap envelopes combine the radius-d disk constant d inverse
power with the genuine annulus inverse power on d<r<=M. Both inverse-distance
and inverse-square envelopes are genuinely plane integrable. Their actual
integrals yield the uniform inverse-distance mass at most 2*pi*M and exact
inverse-square mass pi+diskConstant*log(M/d), for positive d<=M.

Actual inverse-power monotonicity proves that every distance at least d and
at least the horizontal displacement, whose horizontal displacement is at
most M, is majorized by these explicit envelopes. Thus no plane-integrability,
logarithm or domination conclusion is assumed. Applications to actual Maxwell
kernel and source fields are separate, with the gap/radius constants explicit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `c5147d34607b31b856dde051293846f422a84c383ed28328cb656748200fb405`. Independent log `lean/logs/PlaneInverseLocal-root-audit.log`, SHA256 `20fbb066694347d079cc5435abd18c2081055be30ad0a615d583afe0f4c7d202`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

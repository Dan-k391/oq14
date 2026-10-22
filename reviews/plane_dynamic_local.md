# Genuine local plane integration for derived kernel bounds

Frozen source: lean/PlaneDynamicLocal.lean.
SHA256: 047447E53F6B609E0FD777938A4A5CDAE89CB59DDE3BB64946018B4260549552.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/PlaneDynamicLocal-final.log.
Independent review is pending.

A genuine measurable spatial kernel with an explicit local bound C/norm(z)^3
is integrated against an actual L1 source supported in the radius-R ball and
separated from the plane by positive d AE. On the radius-T observation disk,
actual distance is at most T+R. The actual translated inverse-cube envelope
then gives genuine kernel-fiber integrability and its explicit mass bound.
Product integrability and genuine Fubini yield actual disk response
integrability and L1 mass at most C*(pi+diskConstant)/d times source L1 mass.

This is an explicit generic analytic lemma: the kernel bound and measurable
kernel are its declared inputs, not a field or operator conclusion. The next
PlaneMaxwellLocal file discharges these inputs for the actual dyadic, dynamic
remainder and magnetic gradient kernels with explicit constants. It does not
claim a moving-gap whole-plane flux theorem or physical finite-stack identity.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `047447e53f6b609e0fd777938a4a5cdae89cb59dde3bb64946018b4260549552`. Independent log `lean/logs/PlaneDynamicLocal-root-audit.log`, SHA256 `2b1e314002fe92437e9ecacc4896cf4a833ab8ac92a4dbb574e7d472fdb40c78`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

# Actual moving-gap coherent source error convergence

Frozen source: lean/SourceHerglotzMoving.lean.
SHA256: 2ACAD707AFAAF2995260F9862FA8677EF5A4AEBEA5BF56207790C449573B2210.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/SourceHerglotzMoving-final.log.
Independent audit pending.

Actual whole-plane electric and magnetic coherent constants are proved
nonnegative at their physical geometry. A genuine coordinate L1 source
error bounded by C*a^3 and an actual point coefficient bounded by A/a imply
quantitative bounds (C*A)*CE(gamma*a)*a^2 and the analogous magnetic term
for the actual integrated coherent differences. The density and incident
coefficient are conjugated in the correct respective cross-product slots.
The previously derived actual constant limits then prove both actual
whole-plane L1 coherent errors tend to zero as a decreases to zero.

Premises concern actual source support/gap, the actual source L1 error,
incident point inside the enclosing ball and its coefficient bound. No
flux, field, tail or operator convergence conclusion is assumed. These
are generic actual source stability theorems; discharge of the source error
and geometry from the constructed finite-ball inverse family, and the
actual finite incident Gram construction, remain subsequent work. Physical
finite-stack Green identification remains separate.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `2acad707afaaf2995260f9862fa8677ef5a4aebea5bf56207790c449573b2210`. Independent log `lean/logs/SourceHerglotzMoving-root-audit.log`, SHA256 `48f65145b30babaebbfb4ff731b8c501a54b749c4cadffd35a1341e55cc13203`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

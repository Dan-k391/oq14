# Actual finite-ball continuous plane representative

Frozen source: lean/FiniteBallPlaneFields.lean.
SHA256: 654060B7DD9B6A780EA4AE599BB0D910F4B33F48D4FF6AB42074ABA114DE7F70.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/FiniteBallPlaneFields-final.log.
Independent audit pending.

Actual finite-ball geometry and a positive plane gap imply continuity of the
literal complete electric and magnetic fields on an open strip around the
plane. The literal material electric field agrees almost everywhere on that
strip with this ordinary integral representative. Any other continuous strip
representative of the same material field has exactly the same plane trace;
the proof uses equality on the open strip, not restriction of a three-dimensional
almost-everywhere identity to a null plane. The magnetic partner is already
the literal ordinary integral field. The complete plane flux is definitionally
the normal complex Poynting expression of these representatives. Applied to
the actual inverse in FiniteBallWeak, this ties the proved material weak
Maxwell pair to the legitimate plane fields used by FiniteSpherePlaneLimit.
No physical finite-stack Green identification is asserted.

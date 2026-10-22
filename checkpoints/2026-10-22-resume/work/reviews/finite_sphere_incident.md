# Actual finite sphere illumination bounds and weighted forcing

Frozen source: lean/FiniteSphereIncident.lean.
SHA256: 0FF9EBBCB3688410C37ADD333C82006661F0600123FD6B417E42AC8D2F471C2A.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all nine reports standard-only. Log: lean/logs/FiniteSphereIncident-final.log.
Root independent complete-source mathematical audit and pinned compiler PASS: exit 0, no warnings, standard-only foundations.

The actual differentiated sphere integral has operator norm at most
A*abs(k)*surfaceMass for amplitude bounded by A. The actual J derivative
therefore has norm at most entryBound(k)*abs(k). The literal reflection
map has operator norm at most 3 (a sufficient, deliberately loose bound),
and the actual parity reaction derivative has norm at most
2*entryBound(k)*abs(k), including the true reflected chain derivative.

Literal finite parity electric fields have amplitude at most entryBound(k)
times the actual sum of coefficient norms and derivative norm at most
2*entryBound(k)*abs(k) times that mass. Coefficient mass at most A0/a thus
derives the amplitude and derivative constants used in the small-sphere
inverse estimates. No derivative bound is assumed for the fields themselves.
The fields are genuinely locally L2, including at the point centers;
IncidentLocalization constructs the actual material-weighted global L2 datum
and its physical-coordinate representative. Compact support is required only
of the material coefficient, not of the incident Herglotz field.

Both global Maxwell equations were independently derived earlier in
FiniteSphereMaxwell. This file supplies neither Gram interpolation nor
coefficient control for a constructed channel, and does not identify a
physical finite-stack Green kernel.

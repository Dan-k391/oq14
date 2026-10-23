# Actual source-variable differential continuity and parity kernel bounds

Frozen source: lean/SphereParityDifferential.lean.
SHA256: B59F47A122DC8918FF6862693C6F1DBA5456E5688E06F1B2BA59FB13AAEBC694.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all ten reports standard-only. Log: lean/logs/SphereParityDifferential-final.log.
Independent audit pending.

The actual J and K coordinate derivatives are continuous functions, derived
from their literal differentiated sphere moments. The actual electric and
magnetic parity derivatives are continuous in the source variable; finite-
dimensional continuous-linear-map reconstruction from the genuine coordinate
basis proves continuity of the full Frechet derivative in that variable.
The actual magnetic point kernel has derivative norm at most entryBound*abs(k),
its parity coordinate derivative has that same bound, and its full Frechet
norm is at most 3*entryBound*abs(k). The bound is deliberately sufficient
rather than sharp. Every differential fact is derived from actual kernels.

These facts supply actual measurability and domination for density/curl
interchange; no operator continuity or desired density PDE identity is
assumed. Physical radial-stack Green identification is outside this module.

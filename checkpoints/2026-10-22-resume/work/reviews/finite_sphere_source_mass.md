# Actual shrinking finite-ball physical source masses

Frozen source: lean/FiniteSphereSourceMass.lean.
SHA256: 7319DCFD874AC1AB073872A392ABDECA3AD576E9C63E8BA8962D4D73E54A935E.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all two reports standard-only. Log: lean/logs/FiniteSphereSourceMass-final.log.
Independent audit pending.

The literal finite-ball polarization trial source has actual L1 mass at most
3*totalVolume(rho)*chi*A*a^2, derived from its exact indicator definition,
actual ball volumes and the actual polarization bound. No cancellation or
disjointness is needed for this upper bound. The actual material inverse
source mass is at most that trial constant plus the absolute actual source
error constant, times a^2, for 0<a<=1. Its actual source L1 error is derived
from the existing inverse estimates, and the elementary triangle inequality
supplies the mass bound. The absolute error constant safely covers all signs.

These estimates supply genuine source smallness for moving-gap quadratic
flux bounds. Incident center amplitudes and existing constructed inverse
estimates are explicit; the next wrapper specializes them to literal finite
Herglotz illuminations. Physical finite-stack identification remains separate.

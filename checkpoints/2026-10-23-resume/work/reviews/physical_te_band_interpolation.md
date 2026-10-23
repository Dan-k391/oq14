# Actual finite TE band and physical orthonormal inputs

Frozen source: lean/PhysicalTEBandInterpolation.lean, SHA256 0816D933976ADFAD55D532E9C6E3CB93BB24FD0144739803FAB7B6BBAC48C265.
Author final pinned compiler/object PASS: exit 0, no warnings, one standard-only report. Log: lean/logs/PhysicalTEBandInterpolation-final.log. Independent audit pending.

For every finite list of arbitrary vector-jet targets at distinct edge points (r,y_j,0), r nonzero, this constructs a common finite TE band with actual support in even degrees 2 through L. The actual physical transverse sphere L2 incoming inputs are orthonormal, and all literal (Ez,Hx,Hy) jets equal their targets divided by one common positive square root. Coefficients, finite band, normalization, kernel corrections and interpolation are constructed from the prior actual field and power theorems. No desired interpolation, Gram identity or power formula is assumed. Unit vacuum normalization, edge geometry and intrinsic proper-half-turn symmetry remain explicit. Named even-m basis equivalence, actual finite-stack scattering lift and complete OQ14 closure remain open.

# Actual angular-uniform TE magnetic bounds

Frozen source: lean/RegularTEMagneticBounds.lean, SHA256 7C01FC6E9ED7F62C75E9023B5380966F3904F056FA22902403BD5A07FBC9EBBB.
Author final pinned compiler/object PASS: exit 0, no warnings, two standard-only reports. Log: lean/logs/RegularTEMagneticBounds-final.log. Independent audit pending.

For each fixed actual homogeneous harmonic polynomial, the actual incoming/outgoing TE magnetic field is eventually bounded by C/r uniformly over the sphere; its actual radial component is bounded by C/r². The proof uses actual tangential and radial Riccati traces, actual Hankel value/derivative limits, compact angular polynomial bounds and the exact triple-cross decomposition. Adding the actual incoming/outgoing components gives the same bounds for the literal entire regular TE wave. No decay or convergence conclusion is assumed. Constants and cutoff depend on the fixed degree and polynomial; no all-degree uniformity is claimed.

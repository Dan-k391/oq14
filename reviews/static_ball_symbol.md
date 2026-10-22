# Actual uniform-ball Hessian Fourier symbol

Source: `lean/StaticBallSymbol.lean`.
SHA256: `61ACC6A578026F8192C0EB679F152356F1B80658210E928D6D1CA53932520CB1`.

Author final pinned Lean 4.19 compiler and object emission pass with exit 0,
no warnings, and all eight reports using only propext, Classical.choice, and
Quot.sound. Log: `lean/logs/StaticBallSymbol-final.log`.
Root independent full-source mathematical and pinned compiler review PASS
at the same hash, no warnings and all eight standard-only reports.
Independent log: `lean/logs/StaticBallSymbol-root-audit.log`.

A genuine scalar L2 element represents the actual open-ball indicator.
The explicit Hessian's pointwise symmetry and actual AE trace identity imply
the corresponding equalities of genuine L2 elements and their actual Fourier
transforms. Combining these with the previously proved weak derivative Fourier
relation gives the full symbol -xi_i xi_j / norm(xi)^2 times the Fourier
transform of the actual ball indicator. The frequency origin is discarded
only using its actual null measure.

The rank-one matrix identity is proved algebraically from symmetry, trace,
and the actual derivative relation. It does not assume a Green or Newton
convolution identification. Comparison with the existing Newton operator is
the next separate construction.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `61acc6a578026f8192c0eb679f152356f1b80658210e928d6d1ca53932520cb1`. Independent log: `lean/logs/StaticBallSymbol-root-audit.log`; log SHA256 `1ee4a1753b74251c1eb2ce5475b046bb976bcebe0eaff38c2147d8cbdd5ac8ce`. This certifies the stated scope, not either complete OQ14 construction.

# Actual sphere-integral reaction kernel Lipschitz bounds

Frozen source: lean/SphereReactionLipschitz.lean.
SHA256: 1364AFA796E9E5D9B62BD965E7CD0AD8BC6CDB4E2D0186A7F2F5C6E9C7C2B274.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports use only propext, Classical.choice, and Quot.sound.
Log: lean/logs/SphereReactionLipschitz-final.log. Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

The actual complex exponential on the imaginary axis is proved globally
Lipschitz with constant one using its actual derivative and the mean-value
bound. Cauchy-Schwarz transfers this to each actual plane wave. Integrating
the genuine transverse amplitude over the genuine sphere surface measure
gives a derived global Lipschitz bound for J. The explicit reflected electric
and magnetic parity kernels then have source-coordinate Lipschitz constant
entryBound(k) times absolute(k). No kernel derivative or continuity conclusion
is assumed.

This concerns the literal explicit sphere-integral parity kernels. Equality
with a physical finite-stack spatial Green kernel remains separate work.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `1364afa796e9e5d9b62bd965e7cd0ad8bc6cdb4e2d0186a7f2f5c6e9c7c2b274`. Independent log `lean/logs/SphereReactionLipschitz-root-audit.log`, SHA256 `6603125f2b5290b06ecbca9dbce5f3c58297a78e8ea4da61557a6e6d59fd783b`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

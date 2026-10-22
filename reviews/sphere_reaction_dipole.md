# Actual integral reaction dipole estimates

Frozen source: lean/SphereReactionDipole.lean.
SHA256: 3D321D50EDE6F203A32019661D4B0FC3721F9387A6856BEF29CDCE6C4970B793.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports use only propext, Classical.choice, and Quot.sound.
Log: lean/logs/SphereReactionDipole-final.log. Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

Genuine integrability of each explicit parity reaction kernel times an
actual L1 source is derived from the kernel bound and actual continuity.
The actual integral is bounded by entryBound times actual source L1 mass;
the actual integral difference is bounded by entryBound times actual source
L1 difference. For a source AE supported in a radius-R ball, replacing the
source distribution by its actual moment has error at most the derived
kernel Lipschitz constant times R times actual L1 mass.

The actual constant-ball L2 source is then specialized using its derived
actual integral moment and actual mass volume(ball)*norm(P). No response,
Green convergence, point-source, or moment replacement conclusion is supplied.
These are literal explicit parity kernels, whose identification with a
physical finite-stack Green kernel remains separate work.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `3d321d50ede6f203a32019661d4b0fc3721f9387a6856bef29cdce6c4970b793`. Independent log `lean/logs/SphereReactionDipole-root-audit.log`, SHA256 `7409f08566a6429deebb726279c9f749afa972293181e770dc5a4109e2c5e295`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

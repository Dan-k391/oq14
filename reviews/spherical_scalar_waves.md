# Independent audit: SphericalScalarWaves

Frozen source: lean/SphericalScalarWaves.lean.
SHA256: 12D507AB4BD079E3C83F16C1814C3B76DB22F785F5386DCCCA2160FC0EC6852E.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all seven reports standard-only.
Log: lean/logs/SphericalScalarWaves-independent-continuation.log.

The literal radial quotient of U(qr) is smooth at positive radii from actual
complex differentiability. Its actual second derivative acquires q squared,
and its literal radial ODE is proved. Multiplication by an actual homogeneous
harmonic polynomial then yields the actual spatial scalar Helmholtz equation.
The final regular and outgoing theorems instantiate the actual psi/psiD and
xi/xiD derivative equations. No scalar Helmholtz equation is a premise of
those two final theorems.

Nonzero q and x are required. The regular expression in this file is not
yet a value at the origin; the separate solid series supplies that extension.
No Maxwell or interface/Green reconstruction is claimed here.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `12d507ab4bd079e3c83f16c1814c3b76db22f785f5386dccca2160fc0ec6852e`. Independent log `lean/logs/SphericalScalarWaves-independent-continuation.log`, SHA256 `08dde429f9e4e018ec19ef9d659fb256d3a472023ce22c3a915c5f6a21b7b3ca`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

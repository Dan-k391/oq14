# Exact moments and exterior fields of actual constant-ball sources

Frozen source: lean/StaticBallDipole.lean.
SHA256: FC42E2E1AB48CC0EF5401B08469163E2F805FF0257AAA0FFC60091AE083A748A.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/StaticBallDipole-final.log.
Independent review is pending.

The genuine L2 constant-ball source has integrable physical coordinates;
the actual coordinate integral is ball volume times its polarization.
The finite-sum coordinate moment is the actual sum of these volume moments.
The actual previously identified Newton operator outside a positive-radius
ball is proved AE exactly equal to the static Hessian kernel applied to
this volume moment. The volume normalization is 4 pi R cubed / 3, and the
static kernel is the Hessian of 1/(4 pi norm x). No dipole approximation or
operator identity is supplied as a hypothesis.

This is the literal static Newton field outside the source ball. Dynamic,
reaction, physical finite-stack, and plane-integral estimates are separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `fc42e2e1ab48cc0ef5401b08469163e2f805ff0257aaa0ffc60091ae083a748a`. Independent log: `lean/logs/StaticBallDipole-root-audit.log`; log SHA256 `0441f72623646b9e2db3d1d4b94010314e006e8670a0f3c22a9df9b7eda4ab1e`. This certifies the stated scope, not either complete OQ14 construction.

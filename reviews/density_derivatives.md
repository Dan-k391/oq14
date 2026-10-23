# Genuine derivatives through density integrals

Frozen source: lean/DensityDerivatives.lean.
SHA256: 6ADB054725316F4817E5F3DCD034413C766E3514B19F75AF2D5C9B9A501772C7.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/DensityDerivatives-final.log.
Independent audit pending.

A genuine integrable scalar density and actual kernel differentiability,
source-variable continuity of the real Frechet differential, uniform
differential bound and actual kernel integrability yield the true derivative
of the actual source integral. The derivative integrand is genuinely
integrable. Coordinate derivatives evaluate this integral and are themselves
actual integrable source expressions. The proof applies mathlib's dominated
Frechet differentiation theorem with the explicit norm-density envelope;
no derivative/interchange or operator continuity conclusion is assumed.

These are generic actual-kernel hypotheses. SphereParityDifferential and
ParityPlaneFields discharge all of them for the literal parity kernels in
the subsequent density Maxwell theorem. No physical radial-stack Green
identification is claimed.

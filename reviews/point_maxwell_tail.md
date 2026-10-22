# Actual point Maxwell column plane tails

Frozen source: lean/PointMaxwellTail.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all eight reports standard-only. Log: lean/logs/PointMaxwellTail-final.log.
Independent audit pending.

The fields are genuine individual dyadic electric and magnetic gradient
columns centered at points y and z in a fixed ball of radius R. Their
explicit transverse leading fields, inverse-square errors and inverse-radius
bounds are derived from actual kernel formulas. No integrable-density or
Dirac-source surrogate is assumed for these point columns.

For arbitrary real electric frequency k and magnetic frequency l, the
leading normal cross product vanishes on the plane. The actual mixed
normal complex flux is bounded by an explicit inverse-cube envelope outside
radius max(2R,2). This includes the k/-k cross terms needed by the genuine
Herglotz sphere-integral incoming/outgoing identities. All bounds are
uniform in the two source centers inside the fixed ball and in column
indices. No far-field or flux estimate is supplied as a premise.

Herglotz/finite-center assembly and physical finite-stack identification
remain further constructions.
SHA256: 7CE009F972BC1474F2E3ADB8C085FB847F7BAF1B6B07FE7DB4B61162AD9F45FE

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `7ce009f972bc1474f2e3adb8c085fb847f7baf1b6b07fe7db4b61162ad9f45fe`. Independent log `lean/logs/PointMaxwellTail-root-audit.log`, SHA256 `fc029aff6323767604485414ed43a01dcbdc84823cad87cab8fd8f930306c1c6`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

# Actual Lagrange basis and exponential coefficient envelope

Source: `lean/PolynomialGridInterpolation.lean`.
SHA256: `8FDA78A7CE3B0FD3AE619571EE121D4E0B4BFC8FD6A4EFEEBB7C577155A4CABB`.

Author final target plus object compiler exit 0, no warnings. Object 346176 bytes. Eight selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/PolynomialGridInterpolation-final.log`. Forbidden-token scan passed.

The literal coordinate Lagrange basis is the actual product over all other nodes of C(node_a-node_b)^(-1)*(X_i-C(node_b)). Actual algebra identifies it with the pinned univariate Lagrange basis evaluated at spatial X_i. Genuine finite Lagrange interpolation gives the actual polynomial identity for X_i^e whenever e<=l, including l=e=0.

The actual coefficient norm product/triangle bounds and nodes in [0,1) bound each basis coefficient norm by the literal positive weight

    w_l(a)=2^l (l+1)^l/[a! (l-a)!].

No coefficient or denominator estimate is assumed. The exact denominator product is supplied by the independently proved literal-node theorem. The actual binomial/factorial identity then proves

    sum_a w_l(a)=4^l (l+1)^l/l! <= 4^l exp(l+1).

The final inequality follows from the actual nonnegative exponential series, not an asymptotic premise. This is a true exponential degree envelope and will be tensorized over three actual coordinates to bound arbitrary actual bounded-degree spatial polynomial coefficients from their grid values. That tensor identity and actual normalized harmonic representative application are separate successors.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `8fda78a7ce3b0fd3ae619571ee121d4e0b4bfc8fd6a4efeebb7c577155a4cabb`. Independent log `lean/logs/PolynomialGridInterpolation-root-audit.log`, SHA256 `15821d25dc8a1cad0ed1ba69ba29d6f84b5e0c2f87476e1d1736c5e90b7ccd6e`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

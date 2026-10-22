# Genuine differentiation of the actual summed scalar reaction kernel

Source: `lean/RadialScalarDifferentiation.lean`.
SHA256: `ED7CAF36BF4033656AEB8074C0239C619BBCCE962D005269967A9AA5A47567A3`.

Author final compiler exit 0, no warnings; importable object 440648 bytes. All nine selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialScalarDifferentiation-final.log`.

`series(k,m,n)` is the actual sum of the genuine entire scalar reaction (m,n) components with polynomial degree weight. Actual per-term derivative identities are proved from genuine differentiability of the origin series. The actual full-degree majorant for order (m+1,n) uniformly bounds derivatives on an open complex disk, and actual summability at zero supplies the remaining hypothesis of the genuine derivative-of-series theorem. This proves the actual sum has the claimed left derivative. The right derivative follows from the actual product symmetry.

Induction on derivative order, using actual local equality and derivative locality, proves every iterated left and right derivative identity. A further local equality argument proves that every genuine mixed iterated derivative of the zero-order summed kernel equals `series(k,m,n)` throughout the stated source disks. Radius assumptions are actual pointwise common-stack bounds with R sufficiently large for the fixed compact and derivative order.

At positive real radii the zero-order sum is literally the sum of actual scalarGreen corrections. At zero the function is the genuine analytic origin extension. Evaluation through the continuous linear map on the compact continuous-function space proves that, eventually along the actual physical sampled stacks, every value of the summed actualMap equals the actual mixed derivative of that zero-order summed scalar kernel. Thus the earlier compact uniform series limits really are limits of derivatives of the summed scalar kernel; no unproved interchange is inferred from pointwise convergence.

Spatial angular factors, normalized solid radial factors and physical Maxwell dyadic reconstruction remain separate tasks.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 9 reports using only standard foundations. Final source SHA256 `ed7caf36bf4033656aeb8074c0239c619bbcce962d005269967a9aa5a47567a3`. Independent log: `lean/logs/RadialScalarDifferentiation-root-audit.log`; log SHA256 `dfbb85511cd826f7ea2f79f8f1b7e2feddcbe3b80a612a1600ba65b5eee8a263`. This certifies the stated scope, not either complete OQ14 construction.

# Genuine tangential and toroidal harmonic energies

Source: `lean/AngularHarmonicEnergy.lean`.
SHA256: `F690FAEF0DC1EC73DA4F6BC5BEBB864B7DABAB0227ABC197F97AC060CE9C71F3`.

Author target plus importable object compiler exit 0, no warnings. Object 812904 bytes. Twenty selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/AngularHarmonicEnergy-final.log`. Forbidden-token scan passed.

All vector components are literal real polynomials: gradient, tangential part partial_i P-l X_i P, and toroidal part grad(P) cross x. The actual product Laplacian and the proved degree-(l+m) sphere mean Laplacian identity give twice the actual gradient pairing equal to (l+m)(l+m+1) times the actual scalar pairing. Actual Euler identities and the actual radius-squared unit-sphere identity remove the radial parts. For equal harmonic degree l the genuine tangential and toroidal pairings are l(l+1) times the actual scalar pairing. Distinct-degree pairings vanish by the already proved actual scalar orthogonality. No angular energy conclusion is supplied as a premise.

Actual mixed partial commutation is proved by polynomial induction. The literal toroidal polynomial vector has zero formal divergence and zero radial dot product, and its components retain the actual homogeneous degree, including degree zero. The actual homogeneous mean-partial identity therefore proves the mean divergence of any actual homogeneous polynomial vector with zero radial dot product vanishes. Apply this to Q times the toroidal vector of P: its divergence is exactly the toroidal/tangential mixed dot product. Thus the actual mixed angular pairing is zero, for all homogeneous P,Q without even needing harmonicity. No vector orthogonality, spherical Green theorem, test-separation or completeness premise is used.

This file establishes actual polynomial-integral identities. The separate vector-valued L2 adapter supplies the literal normalized angular fields; neither completeness of tangential vector modes nor spatial Green identification is claimed here.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 20 reports use only standard foundations. Final source SHA256 `f690faef0dc1ec73da4f6bc5bebb864b7dabab0227abc197f97ac060ce9c71f3`. Independent log `lean/logs/AngularHarmonicEnergy-root-audit.log`, SHA256 `966f91366690a412862e98db2d331666a47b43fb0663d8af28ca0f17618eb2b7`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

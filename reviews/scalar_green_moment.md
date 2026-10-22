# Actual scalar Green spherical moment equations

Source: `lean/ScalarGreenMoment.lean`.
SHA256: `5FFC6E3AAC131E2E2CE3BCEFA4E77A3212D4CB8FF020ECFA79E817A173A4411E`.

Author target plus importable object compiler exit 0, no warnings. Object 306336 bytes. Ten selected reports standard-only. Log: `lean/logs/ScalarGreenMoment-final.log`. Forbidden-token scan passed.

The kernel is the literal outgoing phi_k(x-y), and its coefficient is the actual sphere integral against the actual harmonic polynomial restriction. The existing genuine compact representation gives the exact translated compact-test identity, with its exact negative point-source term. Actual polar Fubini, actual test integrability and the already derived harmonic test Laplacian yield the literal radial source equation. For compact smooth radius tests supported at positive radii, its full-line form is

    integral [r^(l+2) U eta''+(2l+2)r^(l+1) U eta'+k^2 r^(l+2) U eta]
      = -eta(norm y) P(y).

Neither an expansion nor a source jump is assumed. Actual translated smoothness and the actual translated scalar Helmholtz equation hold away from x=y. On every finite annulus avoiding norm(y), the genuine moment regularity and compact-test fundamental lemma give the actual pointwise radial equation. This source equation is valid without imposing a moment value or continuity at the singular source sphere; determining the one-sided matching, outgoing/regular coefficients and the angular series is the subsequent task.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 10 reports use only standard foundations. Final source SHA256 `5ffc6e3aac131e2e2ce3bcefa4e77a3212d4cb8ff020ecfa79e817a173a4411e`. Independent log `lean/logs/ScalarGreenMoment-root-audit.log`, SHA256 `43acac74f775ae0ad95735f41e63c836f3e484ba24ab32ded443e611c38500a1`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

# Actual cross-degree harmonic orthogonality

Source: `lean/SphereHarmonicOrthogonality.lean`.
SHA256: `74BCF269BBCFBCDAC9F1F3EF84FF0784D9BB1A28D0BC2E5266EE8B8677F474EF`.

Author target plus importable object compiler exit 0, no warnings. Object 393176 bytes. Seven selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SphereHarmonicOrthogonality-final.log`. Forbidden-token scan passed.

For literal homogeneous formal-harmonic real polynomials p,q of degrees l,m, actual homogeneity gives the actual spherical moment U(r)=r^m C, with C the actual angular pairing. Actual first and second radius derivatives are proved explicitly, including m=0 and m=1. The globally smooth actual polynomial q has genuine zero spatial Laplacian. Substituting it into the existing proved annular weak equation at frequency zero, on the literal annulus 0<r<2, and applying the actual fundamental-lemma/classical upgrade gives the actual radial residual at r=1. The residual is [m(m+1)-l(l+1)]C=0. This coefficient is nonzero for distinct natural degrees, by its actual factorization (m-l)(m+l+1), so C=0. No spectral orthogonality or test-separation premise occurs.

Complexification of the genuine real sphere integral transfers this to the real harmonic restriction pairing. The actual normalized representatives therefore have zero L2 inner product across distinct degrees. Combining this result with already proved within-degree orthonormality proves the genuine orthonormal union indexed by the dependent sum of all finite degree bases. This file does not assume or assert completeness; the separate actual dense-span construction provides that next.

Status: author PASS and root complete-source plus independent pinned compiler PASS; no warnings and all selected dependency reports standard-only. Frozen.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `74bcf269bbcfbcdac9f1f3ef84ff0784d9bb1a28d0bc2e5266ee8b8677f474ef`. Independent log `lean/logs/SphereHarmonicOrthogonality-root-audit.log`, SHA256 `b7ce0e46fc891b15424108606f69e18a187cd2af5fe36cb4ec7727120ba3722e`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

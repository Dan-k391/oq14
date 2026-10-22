# Constructed actual sphere harmonic L2 bases

Source: `lean/SphereHarmonicBasis.lean`.
SHA256: `36D9655FF5B1A1B6D4510EA4D584204376F96F64EBB3339C1EEA4F3094B17C4D`.

Author final target plus object compiler exit 0, no warnings; object 310128 bytes. Fifteen selected reports, including the two finite-dimensional instances, use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SphereHarmonicBasis-final.log`. Forbidden-token scan passed.

The actual polynomial subspace is the intersection of degree-l homogeneity and the kernel of the actual formal Laplacian. Its inclusion into actual bounded-total-degree polynomial space proves finite dimension. Its literal continuous restriction followed by ContinuousMap.toLp defines an image subspace in the actual real L2 space of the volume-induced sphere measure.

The standard orthonormal-basis construction on this genuine finite-dimensional inner product space produces the basis. Actual preimages furnish homogeneous harmonic real polynomial representatives; the exported continuous angular functions have literal integral pairings delta_ij and integral squares one. Their representing polynomials are nonzero. No angular basis or normalization is assumed.

For every degree-l homogeneous harmonic polynomial, the actual L2 basis expansion lifts to equality of continuous sphere functions, using full-support injectivity of the actual continuous-to-L2 map. Hence the union of these finite bases spans a uniformly dense subspace of continuous real sphere functions, by actual Fischer density, and its literal image is dense in genuine sphere L2.

Index l is Fin(actual finrank of the degree-l image). No exact 2l+1 dimension formula, cross-degree orthogonality, rotation invariance, pointwise addition identity, or angular derivative bound is asserted here. These are separate successor dependencies. Density alone is not called orthogonality of the union.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 15 reports use only standard foundations. Final source SHA256 `36d9655ff5b1a1b6d4510ea4d584204376f96f64ebb3339c1eea4f3094b17c4d`. Independent log `lean/logs/SphereHarmonicBasis-root-audit.log`, SHA256 `5ca4ff01052b704f1541f1bbcc367d9694b254ecccf64f4d6a89490b1845edec`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

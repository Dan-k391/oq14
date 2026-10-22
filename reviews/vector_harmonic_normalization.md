# Genuine normalized vector angular harmonics

Source: `lean/VectorHarmonicNormalization.lean`.
SHA256: `C2704B3BDA79E25B84C99AF89D2C37B9F1BA01864639445B5E77CD02A7BE4634`.

Author target plus importable object compiler exit 0, no warnings. Object 595496 bytes. Sixteen selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/VectorHarmonicNormalization-final.log`. Forbidden-token scan passed.

Polynomial vectors are restricted as literal continuous Euclidean three-vectors on the actual sphere, then mapped to the genuine vector-valued L2 space. Actual AE representatives and the pointwise Euclidean inner product identify their L2 pairing with the actual mean of their literal polynomial dot product. This transfers the already derived energies and cross/mixed orthogonality to actual vector fields. For the actual scalar-normalized representatives the same-degree energy is l(l+1) times the literal Kronecker pairing.

Positive degrees are indexed by the dependent sum of Index(l+1). Dividing each actual field by sqrt((l+1)(l+2)), whose positive denominator and exact normalization are proved, gives two actual orthonormal families. The combined toroidal/poloidal family is genuinely orthonormal, including all cross polarizations and cross degrees. Their original field components, complexified, are exactly the angularToroidal and angularPoloidal components used by the actual Debye fields on the unit sphere. Both raw polynomial fields are pointwise tangent, using actual Euler and the literal unit-sphere radius identity. No angular-vector normalization conclusion is assumed.

This is a genuine orthonormal family. Completeness in the tangential vector L2 subspace and spatial Green identification are separate obligations; neither is asserted by this file.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 16 reports use only standard foundations. Final source SHA256 `c2704b3bda79e25b84c99af89d2c37b9f1ba01864639445b5e77cd02a7be4634`. Independent log `lean/logs/VectorHarmonicNormalization-root-audit.log`, SHA256 `22ad2a5ac5394e61095869df0e0cb1bd89efd25a62d188cdcff920a3fea4f83e`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

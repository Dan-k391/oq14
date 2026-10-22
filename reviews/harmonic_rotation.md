# Actual orthogonal polynomial substitution

Source: `lean/HarmonicRotation.lean`.
SHA256: `E564417974E4AEE8E72A7C1615577D35ACA09BA7B3AF12D50B174964BE018642`.

Author final target plus importable object compiler exit 0, no warnings. Object 937240 bytes. Fourteen selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/HarmonicRotation-final.log`. Forbidden-token scan passed.

For an actual real Euclidean linear isometry equivalence L, the substitution is literally aeval of the linear coordinate polynomials sum_j C((L basis_j)_i) X_j. Its actual evaluation is p(Lx). Homogeneity is preserved by the actual homogeneous substitution theorem.

The partial chain rule is proved by polynomial induction. Actual orthogonality of the coordinate rows follows from L preserving the real inner product. Applying the genuine partial chain rule twice and summing the row identities proves formalLaplacian(rotate L p)=rotate L(formalLaplacian p). Thus actual harmonicity is preserved; no rotation-invariance or differential conclusion is assumed.

The final export identifies the literal sphere polynomial restriction after substitution with continuous precomposition by the actual sphere homeomorphism. The already proved genuine volume-induced sphere measure invariance is available to the successor L2 rotation/addition construction. This file does not assert an addition theorem, dimension formula, or cross-degree orthogonality.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 14 reports use only standard foundations. Final source SHA256 `e564417974e4aee8e72a7c1615577d35aca09ba7b3af12d50b174964be018642`. Independent log `lean/logs/HarmonicRotation-root-audit.log`, SHA256 `75e85f63eab134cf4cfdb149eed1df8cdb7bcba89be6aa713be13d6724fb9e88`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

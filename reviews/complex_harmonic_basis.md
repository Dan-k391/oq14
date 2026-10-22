# Genuine complete complex harmonic basis

Source: `lean/ComplexHarmonicBasis.lean`.
SHA256: `738C58A56D66D560D0CF7F46F326413084F342C40E31DF637CE96CFEE662F51E`.

Author target plus importable object compiler exit 0, no warnings. Object 305672 bytes. Ten selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/ComplexHarmonicBasis-final.log`. Forbidden-token scan passed.

The actual continuous linear real-to-complex L2 lift and actual L2 real/imaginary maps are constructed using the genuine pointwise continuous linear maps. Actual AE representatives prove u=lift(Re u)+I lift(Im u). The actual inner product of lifted real functions is the complexification of their actual real inner product, by the genuine Bochner integral conversion. Thus the literal lifted normalized angular vectors are complex orthonormal.

Real linear span membership maps into the actual complex span by induction. Continuity takes the already proved dense real span into the closure of the actual complex span. The genuine real/imaginary decomposition then proves every complex L2 function belongs to this closure. This constructs a literal complex HilbertBasis and its genuine unconditional L2 expansion. Each vector is identified with the actual continuous-map-to-L2 lift of the original real angular harmonic, and each coefficient of a continuous complex function is its actual angular integral. The final expansion is L2 convergence, not a pointwise, uniform, differentiated or Maxwell expansion.

Status: author PASS and root complete-source plus independent pinned compiler PASS; no warnings and all selected dependency reports standard-only. Frozen.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 10 reports use only standard foundations. Final source SHA256 `738c58a56d66d560d0cf7f46f326413084f342c40e31df637ce96cfee662f51e`. Independent log `lean/logs/ComplexHarmonicBasis-root-audit.log`, SHA256 `9b596bb3082bf4a67c931146c0f3771b2976233f232bf9994cd717c411227e65`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

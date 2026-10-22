# Actual volume-source Maxwell column identities

Frozen source: lean/PointSourceColumns.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all seven reports standard-only. Log: lean/logs/PointSourceColumns-final.log.
Independent audit pending.

Actual integrable volume densities supported in a fixed ball with genuine
positive plane separation give integrable electric and magnetic kernel
column products at every plane point. The literal cyclic magnetic
convolution equals the finite sum of the actual magneticDyadic column
integrals. Both coherent cross products with an arbitrary fixed complex
vector move inside those genuine source integrals; the magnetic source
coefficient is correctly conjugated. The corresponding actual cross
integrands are integrable, with no interchange or representation identity
assumed.

These exact identities support actual density integration of point mixed
flux bounds. Quantitative whole-plane coherent error and physical
finite-stack Green identification remain subsequent constructions.
SHA256: F2AA0D4DF599ED71075C6FEA302E5317FCCA2382DB2646760B7FFE145448B68F

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `f2aa0d4df599ed71075c6fea302e5317fcca2382db2646760b7ffe145448b68f`. Independent log `lean/logs/PointSourceColumns-root-audit.log`, SHA256 `1504cf320f7a96b6d7dd6d76566e02e3b5772a149e161fcd905244ffd87e1e10`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

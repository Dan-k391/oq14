# Actual Maxwell kernel constants and local plane source bounds

Frozen source: lean/PlaneMaxwellLocal.lean.
SHA256: A3D52D73A08EA2B03087D1A266FDAD4FF072BD1607497373B6D26A85E05772AB.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all eight reports standard-only. Log: lean/logs/PlaneMaxwellLocal-final.log.
Independent review is pending.

On an observation disk of radius T and actual source ball of radius R, the
actual separation distance is at most T+R. Elementary inverse-power algebra
turns the genuine dynamic remainder 1/r bound and actual magnetic gradient
1/r plus 1/r squared bound into explicit local inverse-cube bounds. The
actual dyadic kernel combines the genuine static Hessian and remainder.

The generic genuine product/Fubini plane lemma is instantiated with these
actual measurable kernels and derived coefficients. It yields actual local
integrability and explicit L1 bounds for each electric dyadic, dynamic
remainder and gradient source contribution. No kernel, field or operator
bound conclusion is assumed in these final actual-kernel estimates.

These inverse-gap estimates suffice for O(a cubed) source-error fields. They
are deliberately not labelled sharp trial-field estimates: dynamic trial
fields additionally need uniform local 1/r integration and logarithmic 1/r
squared integration. Whole-plane coherent flux and physical finite-stack
Green identification remain separate constructions.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `a3d52d73a08ea2b03087d1a266fdad4ff072bd1607497373b6d26a85e05772ab`. Independent log `lean/logs/PlaneMaxwellLocal-root-audit.log`, SHA256 `12d3e1db7cb8b7b4a64f5fdce946107315bdbfe7106faff3d120888daf28527c`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

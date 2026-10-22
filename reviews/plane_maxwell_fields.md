# Actual full Maxwell field disk masses

Frozen source: lean/PlaneMaxwellFields.lean.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all five reports use only propext, Classical.choice and Quot.sound.
Log: lean/logs/PlaneMaxwellFields-final.log. Independent audit pending.

Actual integrable sources supported in a ball and separated from the plane
by d>0 give genuine local disk L1 estimates for every component of the
literal electric dyadic convolution, electric dynamic remainder sum, and
magnetic gradient convolution. Finite-sum norm inequalities and actual
integrability derive these field estimates from the checked scalar kernel
bounds. The electric error bound is proportional to 1/d; the dynamic
remainder bound is independent of d, and the magnetic bound has only
logarithmic gap growth (when d <= T+R).

Source subtraction is justified by genuine integrable convolutions on the
plane; actual electric and magnetic field differences obey these same
bounds with the actual coordinate L1 source difference. These are local
disk estimates, not the desired coherent whole-plane incident flux closure
or an identification of the finite-stack Green tensor.
SHA256: 4B40A01F28B0033DECC6FF5D82AB8E6D29EAFB1CA042D2319800059D43022CFC
Root independent complete-source mathematical review and pinned compiler PASS: no warnings, all five reports standard-only (October 22, 2026).

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `4b40a01f28b0033decc6ff5d82ab8e6d29eafb1ca042d2319800059d43022cfc`. Independent log `lean/logs/PlaneMaxwellFields-root-audit.log`, SHA256 `832668735e67082f4a813f81b94d81cccf9fd18b0262357200c0f7bd4c71c47a`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

Final whitespace normalization removed extra EOF blank lines only; independent pinned compilation repeated successfully for the final recorded hash.

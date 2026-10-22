# Sharp local Maxwell kernel plane masses

Frozen source: lean/PlaneMaxwellSharp.lean.
SHA256: 1AD7B5A17659FCCFBE7BE074DC09C1048C74BD93A9339790974112629EFDD1C2.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all four reports use only propext, Classical.choice and Quot.sound.
Log: lean/logs/PlaneMaxwellSharp-final.log. Independent audit is pending.

The actual dyadic remainder 1/r bound and actual magnetic gradient
1/r plus 1/r squared bound are integrated on a genuine two-dimensional
observation disk. Actual translated radial envelopes give remainder mass
independent of positive source-plane gap d and gradient mass growing as
log((T+R)/d). Genuine source-product integrability and Fubini turn the
fiber bounds into actual source response L1 estimates. Assumptions are
actual integrable source, support radius R, positive gap d and d <= T+R.
No field convergence or kernel bound conclusion is assumed.

These are local disk estimates. Whole-plane coherent flux with the desired
Herglotz incident field and physical finite-stack Green identification
remain separate constructions.
Root independent complete-source mathematical review and pinned compiler PASS: no warnings, all four reports standard-only (reported October 22, 2026).

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `1ad7b5a17659fccfbe7be074dc09c1048c74bd93a9339790974112629efdd1c2`. Independent log `lean/logs/PlaneMaxwellSharp-root-audit.log`, SHA256 `70c10f2e1a948946a39866fc4d07095ab5c7551a14aa04253f8c84cc738ee688`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

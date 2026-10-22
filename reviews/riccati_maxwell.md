# Independent audit: RiccatiMaxwell

Frozen source: lean/RiccatiMaxwell.lean.
SHA256: 057D5577E55ECC79865FE94623FAAF25B56515F9E9E3872249F42F080BFCA01A.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all six reports standard-only.
Log: lean/logs/RiccatiMaxwell-independent-continuation.log.

Actual smooth radial quotients and true Riccati first/second derivatives
produce the literal scalar Helmholtz equation. Genuine Debye fields then
satisfy both Maxwell curl equations away from the origin. The normalized TM
fields epsilon inverse times N and -I*k times M are checked directly with
actual curls and a nonzero epsilon; this is the normalization used by the
weighted derivative transmission state. Real versions follow by coercion.

The generic hypotheses are actual radial smoothness/ODE derivatives,
dispersion, homogeneous harmonic polynomial data, and nonzero observation
point. TE requires nonzero k. No scalar Helmholtz or Maxwell conclusion is
a premise of the final wave theorems; actual Riccati derivative data remain
explicit generic inputs. Interfaces, radiation and reconstruction are separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `057d5577e55ecc79865fe94623faaf25b56515f9e9e3872249f42f080bfca01a`. Independent log `lean/logs/RiccatiMaxwell-independent-continuation.log`, SHA256 `848de9655a52c7b81b04ef516c6ff2e8bc85302909389fe1541099bc2e110312`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

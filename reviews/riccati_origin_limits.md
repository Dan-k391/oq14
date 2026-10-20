# Actual regular Riccati origin normalization

Source: `lean/RiccatiOriginLimits.lean`.

SHA256: `0B8C8A722180D1FC813C02FD373E719E9D180692CCD9643A10A8F84F2C6277CC`.

Final author compiler exit 0; importable object 262728 bytes; all 14 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/riccati-origin-limits-check.log`.

The genuine entire origin series factors as z^(l+1) times a normalized even series; its derivative factors as z^l times the normalized slope series. Actual summable majorants prove both normalized series continuous at zero and evaluate their values there explicitly. The previously proved equality with actual psi and psiD away from zero transfers the factors to the actual real Riccati basis.

Thus regular(l,r)/r^(l+1) tends to A_l and regularD(l,r)/r^l tends to (l+1)A_l from positive radii, where A_l=2^l l!/(2l+1)! is strictly positive. Positivity of the actual regular function and derivative on a sufficiently small positive-radius neighborhood follows from these proved limits, with no positivity or normalization premise.

Status: root independent full-source audit and compiler PASS, with standard-only reports and no warnings. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 14 reports use standard foundations. Final source SHA256 `0b8c8a722180d1fc813c02fd373e719e9d180692ccd9643a10a8f84f2c6277cc`. Independent log: `lean/logs/RiccatiOriginLimits-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

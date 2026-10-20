# Actual Riccati degree raising

Source: `lean/RiccatiRaising.lean`.

SHA256: `14B756C4D53FFA224EE2264F03DB32DC421FD6A691F9E37F69AFBE151A8F9AF6`.

Final author compiler exit 0; importable object 1117848 bytes; all nine selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/riccati-raising-check.log`.

The cross-degree factorial identity is proved for the actual finite Hankel coefficients. Polynomial coefficient comparison gives the actual finite polynomial raising identity, transported through the genuine inverse-polynomial representation and its proved derivative. Consequently both actual outgoing and incoming Riccati functions satisfy the derivative raising identity away from zero, as does their actual average psi. Its degree-zero value equals the actual complex sine.

No origin regularity, series identification, positivity or logarithmic derivative bound is assumed. The existing Laurent definitions have placeholder values at zero; every degree-raising assertion explicitly excludes zero. A separate convergent series will supply the genuine origin extension.

Status: root independent full-source audit and compiler PASS. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 9 reports use standard foundations. Final source SHA256 `14b756c4d53ffa224ee2264f03db32dc421fd6a691f9e37f69afbe151a8f9af6`. Independent log: `lean/logs/RiccatiRaising-independent-root.log`. The remaining complete Maxwell constructions are outside this audit.

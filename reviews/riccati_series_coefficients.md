# Convergent regular Riccati coefficient estimates

Source: `lean/RiccatiSeriesCoefficients.lean`.

SHA256: `85B49508569BCFB20E15BC24DF28E36176A1B3EAE9B0B754C2EB3DA3D9AA6963`.

Final author compiler exit 0; importable object 606384 bytes; all 11 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/riccati-series-coefficients-check.log`.

The explicit amplitude is `2^l (l+m)! / (m! (2(l+m)+1)!)`; the signed coefficient multiplies it by `(-1)^m`. Factorial algebra proves its degree-raising relation, coefficient recurrence and positive leading normalization. Induction gives the factorial bound `2^m m! amplitude(l,m) ≤ amplitude(l,0)`. This supplies an exponential-series majorant at every argument and another for the differentiated terms on bounded sets.

These are genuine explicit coefficient identities and estimates. Identification of the convergent series with the actual finite Riccati expression away from zero is proved separately, not presumed here. The pinned mathlib trigonometric-series dependency was built without changing its version.

Status: root independent full-source audit and compiler PASS. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 11 reports use standard foundations. Final source SHA256 `85b49508569bcfb20e15bc24df28e36176a1b3eae9b0b754c2eb3da3d9aa6963`. Independent log: `lean/logs/RiccatiSeriesCoefficients-independent-root.log`. The remaining complete Maxwell constructions are outside this audit.

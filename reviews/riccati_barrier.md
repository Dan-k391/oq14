# Actual regular Riccati barrier positivity

Source: `lean/RiccatiBarrier.lean`.

SHA256: `3492F80E8E1DE7A4094A5D28F6DD515C57B6D32ED0CF52D942D46B07C872D593`.

Final author compiler exit 0; importable object 310936 bytes; all nine selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/riccati-barrier-check.log`.

A generic second-order positivity lemma is proved from actual derivatives, a nonnegative potential and strictly positive initial function/derivative values. A hypothetical first nonpositive value is realized as the minimum of a genuine compact set; before it, the derivative is monotone and positive, hence the function is increasing, yielding a contradiction.

The entire Riccati origin extension supplies globally continuous real function and derivative, the actual radial ODE away from zero, and value zero at zero. The previously derived positive origin limits supply the actual positive starting values at a sufficiently small positive radius. Consequently the actual real regular Riccati function and its derivative are strictly positive throughout 0<x≤R whenever R²<l(l+1).

There is no assumed positivity, singular-origin expansion, normalization or Riccati comparison premise in the actual barrier theorem. All initial data comes from the identified convergent series.

Status: root independent full-source audit and compiler PASS, with standard-only reports and no warnings. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 9 reports use standard foundations. Final source SHA256 `3492f80e8e1de7a4094a5d28f6dd515c57b6d32ed0cf52d942d46b07c872d593`. Independent log: `lean/logs/RiccatiBarrier-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

# Actual bounded material integral operators

Source: `lean/BoundedMaterialKernel.lean`.

SHA256: `308E7338056F475F8271320043F3B3F1914227697BEDAF46419773861E695E8E`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All 17 selected reports use only the standard foundations.
Importable object: 632272 bytes.

A bounded continuous two-point scalar kernel is integrated against the
actual input square-root material multiplier. The output is multiplied by
the same actual square root and placed in the genuine L2 space. Integral
linearity proves that this map is a complex continuous linear map; it is not
supplied as an operator in the hypotheses. Matrix entries are assembled
through the existing actual coordinate insertions.

The proof first bounds the actual source L1 mass by square-root material
volume times its L2 norm. The bounded kernel gives a uniform response bound,
and integration over the actual output support gives a second square-root
volume. The resulting operator norm is at most the coefficient bound times
material volume times the sum of the nine entry bounds. The exact component
integral is exported as an AE equality.

The support data consist of an actual measurable finite-volume carrier,
an enclosing ball, and the actual coefficient being zero outside each.
The `ofFiniteBalls` constructor discharges measurability, finite volume,
and enclosing support from literal finite balls and center/radius bounds.
The ball norm wrapper uses the actual volume upper bound sum(r_i^3*4*pi/3).
No separation or conclusion about operator continuity is assumed.

This generic theorem is intended for the explicit smooth parity kernels.
It does not assert that these kernels equal physical finite-stack Green
kernels. Independent review is pending.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 17 reports use standard foundations. Final source SHA256 `308e7338056f475f8271320043f3b3f1914227697bedaf46419773861e695e8e`. Independent log: `lean/logs/BoundedMaterialKernel-independent-root.log`. The remaining complete Maxwell constructions are outside this audit.

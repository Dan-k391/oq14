# Genuine regular Riccati origin series

Source: `lean/RiccatiOriginSeries.lean`.

SHA256: `DCDCDE72D23543F682E07A47390D0687277548ED84F3D5DA10CAF8911DE9392D`.

Final author compiler exit 0; importable object 503800 bytes; all 16 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/riccati-origin-series-check.log`.

The explicit complex series sums coefficients `(-1)^m 2^l(l+m)!/[m!(2(l+m)+1)!]` times `z^(l+1+2m)`. The proved factorial majorants establish summability at every complex argument and uniform summable derivative bounds on every bounded ball. The actual sum is differentiated termwise and is entire.

Finite degree raising is transported to the actual convergent sums by absolute summability, reindexing and the proved coefficient identity. The degree-zero sum is the actual complex sine. Degree induction and uniqueness of ordinary derivatives on punctured neighborhoods identify the sum and its derivative with the actual finite expressions psi and psiD at every nonzero argument. The selected HasSum theorem states the actual series representation of psi directly.

The original Laurent psi has placeholder values at zero, so equality with that definition is explicitly restricted to nonzero arguments. The genuine entire origin extension has value zero. No singular-origin uniqueness, normalization, positivity or logarithmic derivative estimate is presumed.

Status: root independent full-source audit and compiler PASS, with standard-only reports and no warnings. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 16 reports use standard foundations. Final source SHA256 `dcdcde72d23543f682e07a47390d0687277548ed84f3d5da10caf8911de9392d`. Independent log: `lean/logs/RiccatiOriginSeries-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

# Genuine normalized Riccati functions through the origin

Source: `lean/RiccatiBarrierNormalization.lean`.

SHA256: `34A109FE63B1FA1C0B1CFC3D591A264DF39464E8EC580D3E1EB038FA1DA45753`.

Final author compiler exit 0; importable object 367080 bytes; all 14 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/riccati-barrier-normalization-check.log`.

The actual normalized even origin series and slope series define real v and slope everywhere, including the singular origin. Their continuity is proved from the actual convergent series at zero and actual entire Riccati quotient formulas away from zero. The normalized function is strictly positive throughout the closed barrier interval. Consequently y=slope/v is continuous there, has the actual value l+1 at zero and equals x u'/u at positive radii.

The actual Riccati derivative and exact normalized logarithmic derivative are proved from the genuine ODE. The previously derived gamma≤y≤l+1 bound is transferred to this continuous origin extension. No positivity, origin value, Riccati equation, or normalization is postulated.

Status: author compiler PASS; ready for root independent full-source audit and compiler. Source held unchanged pending audit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 14 reports using only standard foundations. Final source SHA256 `34a109fe63b1fa1c0b1cfc3d591a264df39464e8ec580d3e1eb038fa1da45753`. Independent log: `lean/logs/RiccatiBarrierNormalization-root-audit.log`; log SHA256 `3731229717f8c45293b9183ebb28296ca26f0bb1e56619f31749c3c9a603675f`. This certifies the stated scope, not either complete OQ14 construction.

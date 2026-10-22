# Actual regular amplitudes, exponential weights and moving tails

Source: `lean/RiccatiFactorialTail.lean`.
SHA256: `8F0E7B666A7272972FD79FCDF9E8EA8C8A754646CC40B56FBE6234BF5A45103D`.

Author final compiler exit 0, no warnings; importable object 335248 bytes. All seven selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound` (the elementary natural-number comparison needs only `propext` and `Quot.sound`). Exact log: `lean/logs/RiccatiFactorialTail-final.log`. The pinned Tannery dependency was built successfully with unchanged dependency versions; log `lean/logs/Tannery-target-dependency.log`.

Induction proves l!<=(2l+1)!!, so the actual regular origin amplitude A_l is at most 1/l!. The elementary inequality l+1<=2^l controls every fixed polynomial degree weight. Consequently

    (l+1)^k exp(K*l) (A_l*b^(l+1))^2
      <= b^2 (2^k*exp(K)*b^2)^l/l!.

The genuine exponential series proves this majorant summable for every fixed real K, nonnegative fixed b and natural k. No tail convergence or source estimate is assumed.

For any genuinely summable real sequence G, the literal moving sum over R<=4l tends to zero as R tends to infinity. The proof uses actual dominated convergence for series with the summable absolute sequence, and the eventual disappearance of each fixed degree. Nonnegativity is proved separately when G is nonnegative. This supports the actual intermediate reaction range and arbitrary inverse-power weights through increased polynomial degree.

Status: author PASS and root independent full-source mathematical audit plus pinned compiler PASS, exact frozen hash; no warnings and all seven reports standard-only. Root log: `lean/logs/RiccatiFactorialTail-root-audit.log`. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `8f0e7b666a7272972fd79fcdf9e8ea8c8a754646cc40b56fbe6234bf5a45103d`. Independent log: `lean/logs/RiccatiFactorialTail-root-audit.log`; log SHA256 `11eaaf38aafec5358e927268337ef60bec6682e9350149cc8016cd7d01e79791`. This certifies the stated scope, not either complete OQ14 construction.

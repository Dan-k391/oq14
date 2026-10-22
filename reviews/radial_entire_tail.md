# Genuine all-order compact scalar reaction high tails, including the origin

Source: `lean/RadialEntireTail.lean`.
SHA256: `B2DBD5DF9BF27C16CFF0C26423AA0CB7D67E45BEB3ADA69B174D3E291680C046`.

Author final compiler exit 0, no warnings; importable object 275008 bytes. All seven selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialEntireTail-final.log`.

The literal term is the actual (m,n) entire reaction derivative above cutoff 2qR, and zero below. Fixed disk radius b accommodates the compact radius s and the two fixed derivative orders: s+m<=b and s+n<=b. Once R>=b, the actual high cutoff supplies the true degree barrier at b. The genuine Cauchy comparison therefore bounds every term's norm by exp(2b^2) times the actual reaction coefficient norm times regular(l,b)^2.

For every polynomial angular degree weight k, actual weighted norm summability follows from the genuine Chain-derived high tail at the fixed larger source radius b. The actual weighted complex series is also proved summable by that norm majorant. The actual sum of norms is at most exp(2b^2)*weightedTail(k,b).

For every inverse-power order N, the final epsilon theorem proves R^N times this sum of norms tends uniformly to zero for all z,w in the complex disk of radius s. This includes both origin axes through the genuine analytic extension and holds for arbitrary fixed derivative orders. The only stack premises are actual Chain families, q_g<=q, q>=1 and X<=2R. No barrier, summability, derivative bound or all-order convergence is a premise.

These are high-degree scalar radial estimates. The separate actual identification theorem connects their derivatives with scalarGreen at positive real radii. Low and intermediate angular ranges, angular reconstruction, spatial radial divisions, and the physical Maxwell dyadic remain distinct tasks.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `b2dbd5df9bf27c16cff0c26423aa0cb7d67e45beb3ada69b174d3e291680c046`. Independent log: `lean/logs/RadialEntireTail-root-audit-final.log`; log SHA256 `0acc3e9d0273c0bb7a538667c1cb07710d4f4e16abcc4f79a3fd61d2395d46f9`. This certifies the stated scope, not either complete OQ14 construction.

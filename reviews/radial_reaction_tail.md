# Uniform absolute first-derivative scalar reaction tails on annuli

Source: `lean/RadialReactionTail.lean`.
SHA256: `8E9123219889CAC708179748E0CC567E7D90B0895F014CF1E885957AB37EF8C3`.

Author final compiler exit 0, no warnings; importable object 280328 bytes. All six selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialReactionTail-final.log`.

The selected actual zero/one mixed derivative terms are literal complex reaction coefficients above cutoff 2qR, and zero below. Their polynomially weighted norms are proved summable by the earlier actual Chain-derived high-degree tail. The actual sum of norms is at most max(1,1/a)^2 times weightedTail(k+2).

For every fixed inverse-power order N, angular degree weight k, and positive annulus [a,s], the final epsilon theorem proves R^N times that sum of norms tends uniformly to zero, simultaneously for all x,y in the annulus and all four first mixed derivative combinations. The bounds are uniform in every genuine finite Chain family satisfying q_g<=q, q>=1 and X<=2R. No summability, convergence or barrier is assumed.

This proves absolute scalar radial tails on positive annuli. Origin-containing compact control and spatial Maxwell reconstruction are separate tasks.

Status: author PASS and root complete-source mathematical audit plus independent pinned compiler PASS (session 2036), exact frozen hash; no warnings and all six reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `8e9123219889cac708179748e0cc567e7d90b0895f014cf1e885957ab37ef8c3`. Independent log: `lean/logs/RadialReactionTail-root-audit.log`; log SHA256 `7cf6ba4de310ff8abceab87dc128909b4b4bd83086ed4d3dc694fd18b40f8547`. This certifies the stated scope, not either complete OQ14 construction.

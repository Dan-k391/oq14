# Genuine entire scalar power series with factorial coefficient bounds

Source: `lean/EntireFactorialSeries.lean`.
SHA256: `955005376D77270CBD520E0C86205CD317169053C12B74D5D7D247A5F8ACE4FA`.

Author final compiler exit 0, no warnings; importable object 254904 bytes. All seven selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/EntireFactorialSeries-final.log`.

For actual complex coefficients satisfying norm(a_m)<=A/(2^m*m!), A>=0, the literal power series is proved summable everywhere by the genuine exponential majorant. On every fixed disk of radius B>=1, the actual derivative terms a_m*m*z^(m-1) are uniformly bounded by A*B^m/m!. The proof uses m<=2^m and genuine power bounds, including m=0 and z=0.

The genuine derivative-of-series theorem supplies the actual derivative. Genuine summability and reindexing remove the zero leading derivative term and identify that derivative with the shifted coefficient series a_(m+1)*(m+1). Differentiability at every point then proves actual complex analyticity. No derivative bound, termwise differentiation, or analyticity conclusion is assumed.

This is a generic supporting power-series result, used by the actual squared-radius regular factor. It does not assume or prove a spatial PDE by itself.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `955005376d77270cbd520e0c86205cd317169053c12b74d5d7d247a5f8ace4fa`. Independent log: `lean/logs/EntireFactorialSeries-root-audit.log`; log SHA256 `d444cde8b7767031dd0828f21b8c4173ccd003376eb6ac8914976211322daceb`. This certifies the stated scope, not either complete OQ14 construction.

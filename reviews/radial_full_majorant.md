# Genuine full-degree actual scalar reaction majorant

Source: `lean/RadialFullMajorant.lean`.
SHA256: `82D10091F2D26C478203868B4E965238DAEED95F2EA70EE9A93FCBF24A5C9293`.

Author final compiler exit 0, no warnings; importable object 613240 bytes. All five selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialFullMajorant-final.log`.

For fixed compact/derivative disk b and common material/width bounds, the source defines a literal degree majorant as the sum of three genuinely summable sequences: the low factorial majorant, the intermediate exponential/factorial majorant, and a high polynomial-geometric majorant. Its summability and nonnegativity are proved.

Every degree is treated exactly once in the actual bound proof: the literal low condition 2(l+1)<=R; otherwise l<=2qR; otherwise the high range. At a common boundary the proof chooses the intermediate branch. Actual coefficient/Chain estimates prove the low and middle cases. Genuine Cauchy and Gaussian estimates plus the actual Chain-derived barrier prove the high case. For R>=max(4,e*b), exp(-R/2)<=1 removes the remaining radius dependence.

The resulting majorant bounds the actual polynomially weighted norm of every (m,n) scalar reaction derivative, with norm(z)+m<=b and norm(w)+n<=b. Its constants depend only on q,M,d,b,k, not degree, radius or stack. Genuine summability follows for both the actual full weighted norm series and the actual full weighted complex series.

All geometry hypotheses are pointwise at the selected radius: actual Chain, X<=2R, width X-R<=d and actual material bounds. Thus a physical fixed-width family needs them only eventually; no false all-R X<=2R condition is imposed. No source estimate, tail convergence or dyadic reconstruction is a premise.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 5 reports using only standard foundations. Final source SHA256 `82d10091f2d26c478203868b4e965238daeed95f2ea70ee9a93fcbf24a5c9293`. Independent log: `lean/logs/RadialFullMajorant-root-audit.log`; log SHA256 `90dbc7e7eb161c7907b143c70416175429c2da7434174a295f980a967783fdf0`. This certifies the stated scope, not either complete OQ14 construction.

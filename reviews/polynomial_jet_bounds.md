# Actual coefficient-normalized polynomial compact jets

Source: `lean/PolynomialJetBounds.lean`.
SHA256: `E66C6B24BF3B3B9A50F0CD4D112E19B745A791587024F5C6BCAF039BD8D9BAEC`.

Author final target plus object compiler exit 0, no warnings; object 432032 bytes. Thirteen selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/PolynomialJetBounds-final.log`. Forbidden-token scan passed.

Coordinate derivatives of every order are actually bounded by B on norm(x)<=B, B>=1: the zeroth and first orders follow actual coordinate operator norms, and all higher orders vanish. The genuine higher product rule gives an exponential-in-degree bound for actual monomials. Actual polynomial coefficient expansion and support homogeneity then prove, for any j<=N,

    norm(D^j complexEvaluate(p)(x)) <= coefficientNorm(p) (2^N)^2 (2^N B)^l

when p is homogeneous of degree l. Here coefficientNorm is literally sum over support of absolute real coefficients. No harmonicity or derivative conclusion is supplied as a premise.

Taking actual compact derivative suprema gives

    jetNorm(P,N,b) <= (N+1) coefficientNorm(p) (2^N)^2 (2^N max(1,b))^l.

The final export substitutes this genuine estimate into the actual compact solid-wave derivative bound, including spatial origin. Constants depend only on order, compact ball, frequency, and the explicit polynomial coefficient norm, in addition to the actual factorial-decaying regular amplitude A_l. This provides a sufficient exponential degree envelope; no sharp Markov inequality or uniform L2-normalized harmonic angular basis estimate is claimed. The actual harmonic L2 basis is a separate successor.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 13 reports use only standard foundations. Final source SHA256 `e66c6b24bf3b3b9a50f0cd4d112e19b745a791587024f5c6bcaf039bd8d9baec`. Independent log `lean/logs/PolynomialJetBounds-root-audit.log`, SHA256 `e1a5e05ac5a86321d6ec6ae86c4fd21b01bd54cb6e3b38aa24217169f66a3e40`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

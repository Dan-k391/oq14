# Actual intermediate-window scalar source bound

Source: `lean/RadialIntermediateBound.lean`.
SHA256: `6A474CFF9AEB0FB2038C762D5B76B7080B461E53F4EF88C78B69B69C4C16E181`.

Author final compiler exit 0, no warnings; importable object 287624 bytes. All three selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialIntermediateBound-final.log`.

This source reuses the actual frozen `HankelIntermediateBounds` estimates. Set h(q)=2+2q*log(4q), C(q)=1+(1+2q)^2 and A(q)=4q^2+2q. For R<=x<=2R and l<=2qR, the actual fundamental matrix Frobenius square is bounded by C(q)*exp(2h(q)R).

For R>=1, the same degree cutoff gives l(l+1)<=A(q)R^2. The actual Chain cost bound therefore yields totalCost<=(2M+A(q))d when X-R<=d, M>=0 and actual layer parameters obey 1<=sigma_g<=M and q_g^2<=M. Combining the actual incoming/source coefficient energy estimate gives

    norm(gamma_l) <= C(q)^2 * exp(4h(q)R+(2M+A(q))d).

All premises are literal geometry and material bounds; no source coefficient estimate or transfer conclusion is assumed. This is an explicit sufficient common-stack bound. The factorial tail successor will handle the moving lower cutoff in the intermediate range. No spatial Maxwell expansion is claimed.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 3 reports using only standard foundations. Final source SHA256 `6a474cff9aeb0fb2038c762d5b76b7080b461e53f4ef88c78b69b69c4c16e181`. Independent log: `lean/logs/RadialIntermediateBound-root-audit-final.log`; log SHA256 `1d5a6dfb0ea8c7322f2fa879712f31a8462ad396cc2edcb78bb36560b985f1ac`. This certifies the stated scope, not either complete OQ14 construction.

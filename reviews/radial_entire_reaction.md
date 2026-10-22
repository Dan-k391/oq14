# Actual entire scalar reaction and all mixed derivatives

Source: `lean/RadialEntireReaction.lean`.
SHA256: `080E0B6F979B03CB3E920B5567A361E864D3BDFFBAB0B74C7E3D99B7801411CC`.

Author final compiler exit 0, no warnings; importable object 243992 bytes. All seven selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialEntireReaction-final.log`.

The complex two-radius reaction is defined literally as gamma*origin_l(z)*origin_l(w). It equals the actual scalarGreen correction at every pair of positive real radii. Its zero-axis values follow from the proved actual origin value, without modifying or identifying the raw finite Riccati formula at zero.

Every (m,n) component is proved equal to the genuine iterated complex mixed derivative. A separate genuine real differentiation argument proves the same identification for all real mixed derivatives of the actual scalarGreen correction at positive radii.

The actual Cauchy/Gaussian bounds give the degree-independent comparison

    norm(component_mn(z,w))
      <= exp(2b^2) * norm(gamma) * regular(l,b)^2,

provided norm(z)+m<=b, norm(w)+n<=b, b>0 and b^2<l(l+1). The enlarged radius b is fixed as a function only of compact radius and derivative orders, independent of R, degree and actual stack. This estimate includes z=0 or w=0 through the genuine analytic extension.

This is the entire extension of the actual scalar radial reaction. It is not a spatial Maxwell dyadic expansion; angular factors, spatial radial divisions and vector reconstruction remain separate.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `080e0b6f979b03cb3e920b5567a361e864d3bdffbab0b74c7e3d99b7801411cc`. Independent log: `lean/logs/RadialEntireReaction-root-audit-final.log`; log SHA256 `971015fad95c722a6c3b4a73b4f33c9a99f0b260d3c00d72f83d956b927b39db`. This certifies the stated scope, not either complete OQ14 construction.

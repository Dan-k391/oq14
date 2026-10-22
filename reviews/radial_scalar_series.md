# Actual all-degree scalar reaction series limit

Source: `lean/RadialScalarSeries.lean`.
SHA256: `50A096E821E93308F8E84161CF5D3D9CC55CC3E90D1782965A3A0A2A68A4B7D9`.

Author final compiler exit 0, no warnings; importable object 193064 bytes. All six selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialScalarSeries-final.log`.

Induction on the actual fixed Segment list transfers its literal material parameter bounds to every physical layer at every positive starting radius. Actual sampled radii are RadialPhaseLimit.radius(j)=2*pi*(j+1), and the physical layers are the untrimmed `RadialFiniteLimit.layers` with outer radius R+width(gs).

The source invokes the actual proved `RadialPhaseLimit.actual_gamma_limit`, not a generic coefficient limit premise. Multiplication by the genuine entire regular derivatives gives the actual fixed-degree mixed reaction limit. Eventually R>=width(gs), R>=4 and R>=e*b; therefore the actual physical stack satisfies the full majorant hypotheses. No false all-R X<=2R hypothesis is imposed.

The genuine fixed summable degree majorant proves eventual summability of the actual weighted complex series and summability of its explicit limiting series. Actual dominated convergence for series then proves the all-degree scalar series tends to that limiting series, for arbitrary fixed polynomial angular weight and mixed radial derivative orders. The fixed complex points can include zero through the genuine origin extension.

This is a pointwise scalar mixed-derivative series limit. A separate sup-norm successor establishes uniform compact convergence. Physical angular/dyadic reconstruction and its normalization remain separate.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `50a096e821e93308f8e84161cf5d3d9cc55cc3e90d1782965a3a0a2a68a4b7d9`. Independent log: `lean/logs/RadialScalarSeries-root-audit.log`; log SHA256 `012f19018f170e95448ae475959991ffb42f2db9f52a225c21d6830ca5994415`. This certifies the stated scope, not either complete OQ14 construction.

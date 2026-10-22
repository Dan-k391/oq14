# Actual low-range scalar reactions and uniform angular tails

Source: `lean/RadialLowTail.lean`.
SHA256: `C2C0CBA4EE0EB93A751E6B342658BF33A1DEBBE872DC40AA57A7BBAE4A548B84`.

Author final compiler exit 0, no warnings; importable object 277224 bytes. All eight selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialLowTail-final.log`.

The literal low degree condition is 2(l+1)<=R. Its actual angular estimate supplies c=1/2 in `RadialSource.gamma_low_range`. Actual Chain and common material bounds, together with width X-R<=d, then give the radius-independent actual coefficient bound B=(4/(1-1/4))^2*exp((2M+1/4)d).

Genuine Cauchy estimates give every fixed mixed derivative a common factorial amplitude majorant, multiplied by B*exp(b^2). The actual polynomially weighted norm series is proved summable from the genuine factorial series. Its actual angular tail above T<=4l is bounded by that fixed factorial sequence's moving tail.

The final epsilon theorem proves these angular tails tend uniformly to zero as T tends to infinity, simultaneously for R>=1 and all points of the fixed complex disk. The fixed b accommodates the compact radius and the two derivative orders, including the origin. All geometry/material premises are actual Chain, common bounds and width, with no source estimate or tail convergence as premise.

The pointwise coefficient limit and the full scalar series assembly are separate successors. No spatial Maxwell dyadic identification is claimed.

Status: author PASS and root complete-source mathematical audit plus independent pinned compiler PASS, exact frozen hash; all eight reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `c2c0cba4ee0eb93a751e6b342658bf33a1debbe872dc40aa57a7bbae4a548b84`. Independent log: `lean/logs/RadialLowTail-root-audit.log`; log SHA256 `6f1c7072be10882e9cec4dd61bda268bcacd9498f7772c48a811a28f5fa26497`. This certifies the stated scope, not either complete OQ14 construction.

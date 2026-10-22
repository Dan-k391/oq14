# Independent audit of actual fixed finite radial-stack limits

Source: `lean/RadialFiniteLimit.lean`.
SHA256: `C9D404B3C08FFCDE8AE16185FDC638E59D18339C0AB2A9F1CE5348AFE90F76F4`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Exit 0, no warnings, and all ten selected reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/RadialFiniteLimit-independent-continuation.log`.

The propagated state is a recursive sequence of actual initial-value radial
solutions at actual shifted radii. The finite-list limit is derived by
induction from the genuine single-layer comparison, including convergence
of the intermediate initial states. No propagated-state limit is supplied
as a premise. Actual geometric Layer values are also constructed, their
finite Chain property is proved, and each segment state is identified with
the actual previously constructed transfer matrix.

The high/low quarter-wave widths are literal pi/(2q) and pi/2. Their constant
reference pair is identified with the actual ordered product. Repeating
this pair gives the exact diagonal state factors (-q/sigma)^n and
(-sigma/q)^n. The corresponding fixed finite actual physical radial
propagation converges to these factors as the common radius tends to infinity.

Scope: fixed degree l, fixed finite segment list or fixed pair count n,
positive q and sigma, fixed widths, and common radius tending to infinity.
There is no uniformity in increasing degree/pair count, no all-channel Green
limit, and no spatial Maxwell identification in this module.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 10 reports using only standard foundations. Final source SHA256 `c9d404b3c08ffcde8ae16185fdc638e59d18339c0ab2a9f1ce5348afe90f76f4`. Independent log: `lean/logs/RadialFiniteLimit-independent-continuation.log`; log SHA256 `1d0dab57e2017b5856d9a5428a84c37eed00f483e5691958ae8648cdac2cd7b3`. This certifies the stated scope, not either complete OQ14 construction.

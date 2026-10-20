# Hankel energy independent audit

Independent whole-source mathematical review and pinned compiler recheck by `fredholm_sol`: PASS.

- Source: `lean/HankelEnergy.lean`.
- Exact SHA256: `5926AD3EA281639191A297FEDD88068F884E116ACFAEEED79461FEE691C9429D`.
- Independent command: pinned Lean 4.19.0 `lake env lean HankelEnergy.lean`, exit 0, no warnings.
- Independent log: `lean/HankelEnergy.independent-fredholm.log`; SHA256 `C11B48869C3131A02B718CDA58CB0511DAFFD42E93D8B07C35CDBD934B4F9916`.
- All fourteen dependency reports use only `propext`, `Classical.choice`, `Quot.sound`.

The energy is the literal squared norm of the actual finite outgoing Riccati--Hankel derivative plus `(1-l(l+1)/r^2)` times the literal squared norm of the actual outgoing function. Its derivative is obtained from the previously proved actual derivative/ODE formulas: the two mixed terms cancel, leaving `2*l(l+1)/r^3 * normSq(xi)`. Thus the sign is correct on positive radius without a degree or asymptotic hypothesis.

The normalization at infinity is derived from the genuine finite inverse-coordinate polynomial. Its derivative tends to zero because it equals `-r^-2` times the actual derivative polynomial at `1/r`; both Hankel squared norms tend to one after the unit-modulus real-frequency exponential and phase factors are removed. The energy therefore tends to two. Monotonicity plus this limit gives the upper bound two for every positive radius, including degree zero.

The low-range hypothesis `l(l+1)<=c^2*R^2`, together with `r>=R>0`, gives the literal lower bound `1-c^2` for the weight. If `c^2<1`, positivity and the already established energy bound then give both asserted actual squared-norm estimates. No uniform asymptotics, energy bound, or monotonicity conclusion is included as an input.

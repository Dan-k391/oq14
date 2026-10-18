# Actual material coefficient in the static block

Source: `lean/StaticCoefficient.lean`. Status: PROVED in Lean 4.19.0 with pinned dependencies.

The coefficient is an actual measurable real function on Cartesian three-space, pointwise nonnegative and bounded above by a finite real constant. The construction forms the actual vector L2 multiplication operator S by sqrt(chi), proves its norm at most sqrt(bound), self-adjointness, and the almost-everywhere identity S squared equals multiplication by chi. Its definition uses the proved L2 integrability of the pointwise product; no multiplication operator is supplied as a hypothesis.

The resulting block is exactly I+S P S, where P is the constructed physical longitudinal Fourier projection from VectorFourier. Its explicit almost-everywhere action is exported. The positive static-block results prove coercivity with constant one, invertibility, and inverse norm at most one. An explicitly norm-small bounded perturbation Q inherits the inverse and residual estimates already proved in StaticVolume.

Validation: clean compilation with no warnings or errors. All 20 theorem exports report exactly `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`. No proof placeholders or custom axioms.

Independent review: hotspots checked the measurable multiplication, coefficient and norm bounds, self-adjointness, square identity, actual weighted-block formula, and concrete instantiation of the positive inverse estimates. No defect found.

Scope: Q is explicitly an abstract bounded perturbation satisfying norm less than one. This module does not identify it with a dynamic Maxwell Green remainder or prove its smallness. The separate identification of P with the Newton-potential convolution is likewise not claimed.

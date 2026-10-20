# RadialMomentWeights verification

Source: `lean/RadialMomentWeights.lean`.
SHA256: `263F3AC62ABA656CA75FD9C81F35ABD499803A2B3C95A994FD724D6EBAB8CD12`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All nine selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The coefficient functions are literal complex powers of the real radius
multiplied by U, UD, and UDD. Genuine derivatives of the actual real-radius
complex powers are obtained by composing the real power derivative with
the continuous real-to-complex inclusion. Actual product differentiation
gives A', A'', and B' for A=r^(l+2)U and B=(2l+2)r^(l+1)U. Ring algebra
proves A''-B'+C=r^l*(r²UDD+2rUD+(k²r²-l(l+1))U), with C=k²r^(l+2)U.
The final exports establish actual coefficient continuity from continuous
U, UD, and UDD. Derivative premises are explicit genuine HasDerivAt facts;
no weak or classical radial equation is presumed.

Independent full-source review requested from root at this hash.

Root completed the independent full-source audit at this hash. Final freeze PASS.

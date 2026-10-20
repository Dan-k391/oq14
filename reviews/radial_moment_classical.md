# RadialMomentClassical verification

Source: `lean/RadialMomentClassical.lean`.
SHA256: `3CA1D5ACA8A0A112360D835EB2A6A89BD145F000B271CDBEC1073CFC21AED53E`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All four selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The explicit weak premise is the whole-real-line integral of the literal
A*eta''+B*eta'+C*eta coefficient functions, for every real smooth compact
test supported in Ioi R. The genuine derivative-representative Green
identity and continuous fundamental lemma prove A''-B'+C=0 pointwise.
The verified coefficient identity and positive exterior radius cancel the
nonzero r^l factor, giving r²UDD+2rUD+(k²r²-l(l+1))U=0. Actual product
differentiation of F=r²UD then yields F'=(l(l+1)-k²r²)U, and F/r²=UD.

The final wrapper instantiates U, UD and UDD with the literal spherical
moment, its first derivative integral and its second derivative integral.
Its genuine smooth exterior-field and continuous angular-test premises
provide all required derivative and continuity hypotheses from the frozen
moment modules. The explicit weak coefficient integral remains a premise
for the PDE-to-weak-moment module to discharge; no weak radial equation is
inferred from exterior smoothness alone.

Independent full-source review requested from root at this hash.

Root completed the independent full-source audit at this hash. Final freeze PASS.

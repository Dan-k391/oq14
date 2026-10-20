# AnnularMomentClassical verification

Source: `lean/AnnularMomentClassical.lean`.
SHA256: `07B24FFA151B4195D68A3A336114FF50CEE634D2432A2A3615F416DE44994BB4`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. Both selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The generic theorem applies the verified genuine one-dimensional Green
identity and fundamental lemma on the open finite interval Ioo R L.
The weak premise is explicitly the whole-line integral of the unchanged
A*eta''+B*eta'+C*eta coefficients for every real smooth compact test with
support in that interval. The actual coefficient derivative formulas and
continuous UDD give pointwise A''-B'+C=0. Positive radius cancels r^l in the
verified coefficient residual identity, giving the classical radial
Helmholtz residual.

The actual-moment wrapper uses the unchanged literal spherical moment,
first moment derivative, and second moment derivative integrals. Only
smoothness on the literal finite spatial annulus and continuity of P are
required to supply their actual derivative and continuity facts. The
literal frozen flux F=r²*momentD then has the required classical flux
derivative and momentD=F/r². The actual PDE weak-moment identity remains
an explicit premise discharged by the separate annular PDE module.

No global exterior extension or finite-interval uniqueness conclusion is
presumed. Independent full-source review requested from root at this hash.

Root completed the independent full-source audit at this hash. Final freeze PASS.

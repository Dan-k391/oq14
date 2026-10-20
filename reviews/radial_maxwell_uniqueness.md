# Independent finite radial Maxwell uniqueness audit

Reviewer: continuation_review_sol. Date: 2026-10-20.

Source: `lean/RadialMaxwellUniqueness.lean`.
SHA256: `7C88C4C3EB8AF1505D3FC1F04CDF9CFC2939F54E1023CC0D862C84434952E512`.

Independent pinned Lean 4.19 compilation completed with exit 0. All six
dependency reports list only `propext`, `Classical.choice`, and `Quot.sound`.
The complete source was read, along with the complete PiecewiseScattering
and MaxwellZeroField sources and the actual piecewise-uniqueness and
finite-radial-partition interfaces. Those latter proof chains already have
separate independent reviews.

Given arbitrary finitely many strictly increasing positive radii, this
module invokes the constructed actual radial partition, not an assumed
geometric certificate. The actual dielectric is assumed AE equal to the
specified positive material value on each literal radial cell. This is a
coefficient specification, not a PDE conclusion. Compact coefficient
support and positive real frequency are explicit. The required seed point
in the exterior cell, outside the prescribed support ball, is actually
constructed by the radial partition theorem.

Exterior Rellich, regional Maxwell localization, weak scalar Helmholtz
continuation, actual adjacent bridge paths, and AE coverage therefore prove
electric AE zero for homogeneous volume fields. The first Maxwell curl
equation then annihilates every compact smooth magnetic test pairing.
Actual local integrability and the distributional fundamental lemma imply
magnetic AE zero. No initial magnetic zero assumption is needed.

The genuine material relation and square-root-weighted L2 source identify
electric zero with homogeneous-unknown zero, without dividing by possibly
zero contrast. The actual static preconditioning and compact remainder
then give invertibility and a unique solution for every L2 volume datum.
Neither a kernel-zero premise nor small support/contrast is assumed.

For classical vacuum incident fields, the final theorem constructs an
actual volume unknown whose total fields satisfy PhysicalFields. That
predicate means actual weak dielectric Maxwell tests, componentwise local
L2 bounds, exterior continuity of the scattered electric representative,
actual material polarization, and an inverse-square Silver--Mueller defect
bound. Incident C1 regularity and the actual vacuum Maxwell equations
supply its hypotheses; physical field existence is not assumed.

The exact scope is any bounded nonnegative compactly supported
susceptibility whose actual dielectric is AE constant on the specified
finite concentric cells. Material values may repeat; the one-interface
case is included. The theorem does not require construction of a global
arbitrary nonradial partition. It also does not by itself provide a
power-normalized scattering operator, whole-plane absolute-flux estimates,
the all-angular-order common-stack Green limit, or the complete channel
counterexample. PhysicalFields is an explicit finite-energy/radiation
Maxwell certificate, not an assertion that all those later constructions
have already been formalized.

No standalone custom axiom/constant declarations or proof-hole tokens occur
in the new source. No proof source was edited. Independent mathematical and
compiler audit: PASS.

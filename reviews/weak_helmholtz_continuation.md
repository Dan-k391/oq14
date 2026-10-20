# Independent weak Helmholtz continuation audit

Reviewer: continuation_review_sol. Date: 2026-10-20.

Source: `lean/WeakHelmholtzContinuation.lean`.
SHA256: `3B4B85AEA7AD17951A92334D6AF86F237B080A09C5C8C014502FB8764A9BBDCB`.
This matches the resume checkpoint exactly, including the final eventual-equality
orientation correction.

Independent execution of the pinned Lean 4.19.0 compiler using
`lake env lean WeakHelmholtzContinuation.lean` completed with exit 0.
All four dependency reports list exactly `propext`, `Classical.choice`, and
`Quot.sound`. The manifest pins mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).

The complete source was read, together with the complete sources of
WeakHelmholtzRegularity, HelmholtzMollifiers, HelmholtzMollifierZero,
LocalAEZeroPropagation, LocalHelmholtzRepresentation,
HelmholtzUniqueContinuation, HelmholtzBallContinuation,
HelmholtzTranslation, AnnularMomentEquation, AnnularMomentClassical,
RadialIntervalFlux, RadialIntervalUniqueness, and HarmonicMomentSeparation.
The underlying definitions of three-dimensional Euclidean space, the actual
coordinate Laplacian, complex normalized bump kernel, and shrinking bump
sequence were also inspected. This is an audit of this proof and its actual
reused interfaces, not a fresh compilation of every transitive dependency.

The weak predicate is the literal integral of `u * (laplacian phi + k^2 * phi)`
against every smooth compactly supported test whose topological support lies
in the domain. It does not contain regularity or continuation conclusions.
Global local integrability supplies actual Bochner convolution regularity.
Actual kernel first and second derivatives pass under the integral; testing
the weak equation with its translated reflection gives the classical
Helmholtz equation on each smaller ball. Kernel radii tend to zero, so this
holds eventually on any fixed strict inner ball.

An almost-everywhere zero neighborhood gives an actual ball on which the
original function is almost everywhere zero. Reflected kernel support
containment then makes the convolution identically zero on a smaller ball,
eventually in the same shrinking sequence. These are actual zero germs,
not almost-everywhere substitutes for the smooth-continuation hypothesis.

For each point in the target ball, the proof chooses a strictly smaller
concentric ball still containing that point. On one common eventual tail,
the genuine mollifiers satisfy both the classical equation and the zero-germ
hypothesis. The smooth ball theorem therefore makes their values zero there.
The normalized-bump almost-everywhere convergence theorem applies to these
same convolutions. Uniqueness of limits gives the original function zero
almost everywhere on the whole ball. The corrected eventual-equality
orientation in the final line is accepted by the independent compiler.

The smooth ball theorem itself derives the radial moment equation from
the spatial PDE, applies finite-interval flux uniqueness using the proved
incoming/outgoing basis Wronskian, and separates all homogeneous harmonic
moments using the proved harmonic-span density and full angular support.
Translation proves the result on balls with arbitrary centers. No solution
analyticity or smooth representative of the original weak function is assumed.

For the domain theorem, openness of zero germs and relative closure follow
from the proved ball result. Preconnectedness propagates a supplied nonempty
germ throughout the open domain. A countable open subcover then combines
the local almost-everywhere equalities into the single domain equality;
there is no invalid uncountable union of null exceptional sets.

The precise scope is a globally locally integrable scalar complex field,
an open preconnected domain, a nonzero complex frequency, the actual weak
equation there, and an actual almost-everywhere zero germ at a point of the
domain. The result is almost-everywhere vanishing on that domain. This does
not itself assert pointwise weak-field vanishing, a smooth representative,
variable-coefficient continuation, interface geometry, or global Maxwell
uniqueness.

The inspected continuation/smoothing sources contain no proof-hole tokens
or standalone custom axiom/constant declarations. No proof source was edited.
Independent compiler and mathematical audit: PASS.

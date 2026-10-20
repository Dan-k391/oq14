# RadialPowerTest verification

Frozen source: `lean/RadialPowerTest.lean`.
SHA256: `703F351FECC90328CF27EBDBEF7295C2D6305578D1BA6124B1DE0B79B45613F1`.

Pinned Lean 4.19 compilation and importable object export completed with exit
0 and no warnings. All 27 selected theorem dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

For a genuine real C1 profile theta, radial(theta)(x)=theta(norm(x)^2) is
proved C1, with actual coordinate Frechet derivative
2*deriv(theta)(norm(x)^2)*x_i at every point, including the origin. A profile
vanishing beyond R^2 yields an actual compactly supported radial function
with support inside the closed ball of radius R. Actual RealTest values are
constructed both on all space and on any region containing this ball.

The coordinate real Poynting vector and the actual radial power are related
by norm(x)*radialPower=sum_i x_i*realPower_i. The exact gradient-test pairing
therefore equals 2*theta'(norm(x)^2)*norm(x)*radialPower, for arbitrary fields.
This is an algebraic and calculus identity; no weak conservation or outgoing
power conclusion is assumed.

The concrete beta is an actual smooth nonnegative bump centered at 2, zero
for q<=1 and q>=3, with beta(2)=1. Its genuine interval antiderivative
theta(q)=integral(q..4,beta) has derivative -beta, is C1, vanishes for q>=3,
and is a strictly positive constant for q<=1. Although the real profile is
constant towards negative infinity, its norm-squared radial composition has
compact support, exactly as proved by the support argument.

For every positive a, scaledCutoff(a) is constant and strictly positive on
the ball of radius a and supported inside the ball of radius 2a. Its exact
testPower is -(2/a^2)*beta(norm(x)^2/a^2)*norm(x)*radialPower. This supplies
actual arbitrary-radius weak radial tests without positing a weak-to-flux
principle or a desired power identity.

Root completed the independent complete-source audit at the frozen hash above and accepted all 27 selected results. Final freeze PASS.

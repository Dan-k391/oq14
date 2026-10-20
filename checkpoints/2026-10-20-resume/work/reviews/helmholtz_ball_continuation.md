# HelmholtzBallContinuation independent verification

Independent reviewer: reciprocity_sol.
Pinned Lean 4.19 independent compiler runs completed with exit 0 for:

- `lean/AnnularMomentEquation.lean`, SHA256
  `FA532332E20AF2F7C6C0831B9C267807D2B6A9B09D189EA6052EEFAB6A323EBB`;
  all three selected dependency reports use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lean/HelmholtzBallContinuation.lean`, SHA256
  `057C984677BC507F9E0F9D727B609FDFECEE9842121202AED893419147C533F1`;
  all four selected dependency reports use only those same foundations.

Both complete sources were read, including the actual test and moment
interfaces reused from SphericalMomentEquation and the finite-interval
flux uniqueness and harmonic moment separation interfaces.

The radial test is the genuine smooth compact spatial function
eta(norm(x))*p(x). Support stays strictly inside the annulus, including
separation from the origin. Local Cartesian Green integration by parts
gives honest global integrability before applying the actual complex
polar integral formula. The harmonic homogeneous polynomial evaluation
and radial test Laplacian give the exact radial weak equation. Expanding
the positive-radius expression and proving test and derivative vanishing
outside positive radii transfers it to the whole real line. Real tests
are included through the actual real-to-complex derivative identities.

The ball result supplies that actual weak equation to the actual annular
moment calculus. A common sufficiently small positive radius has every
moment identically zero near it because the actual field vanishes on a
neighborhood of the center. Genuine finite-interval flux uniqueness then
forces every homogeneous harmonic moment to vanish at every radius in
the ball. The proved harmonic restriction density and full angular
measure support give pointwise zero on every positive-radius sphere.
Normalization of an arbitrary nonzero point recovers zero everywhere in
the ball; the center follows from the original neighborhood equality.

The conclusions require actual smoothness, actual constant complex-k
Helmholtz equation, nonzero k, and an actual zero neighborhood. No radial
ODE, expansion completeness, analytic regularity, or continuation
conclusion is included as an unproved premise. The first independent ball
compile exposed only an omitted zero-function application simplification;
the corrected source at the final hash above compiles and passes the
full mathematical audit. PASS.

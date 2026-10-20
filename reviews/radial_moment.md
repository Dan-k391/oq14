# RadialMoment — actual spherical radius differentiation and decay

Source: `lean/RadialMoment.lean`

SHA256: `EE99E87A6542C05BD07AD2886F5EA51CADE334A43E7FFF996FBB5C2896CD90D2`

Evidence: `lean/logs/radial-moment-check.log`. Final compile exited zero,
created an importable object (478696 bytes), and emitted 17 selected
reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

The actual moment uses exactly AngularPower.Sphere and angularMeasure:
U(r) is the integral of u(rn) P(n), without conjugation or extra surface
radius factors. The exterior field hypothesis is genuine C-infinity on
the open set norm x > R, with R nonnegative; P is continuous on the compact
unit sphere. No derivative domination assumption is imposed on the user.

The compact differentiation helper obtains the uniform derivative bound
from continuity on [r-epsilon,r+epsilon] times the compact sphere and
integrates under the finite angular measure. For the actual field,
epsilon=(r-R)/2 keeps this compact set strictly outside the material ball.
The first derivative is the integral of Du(rn)[n] P(n), and the next
derivative is the integral of D(Du)(rn)[n][n] P(n). Both HasDerivAt
certificates, their exact deriv equalities, and C1 on the exterior
half-line are proved.

Cauchy–Schwarz is applied to the actual continuous sphere functions. For
the spherical mass integral of r^2 times norm u(rn)^2, the resulting bound
is norm(r U(r)) at most sqrt(mass(r)) times the fixed L2 norm of P. Thus
actual spherical mass tending to zero implies r U(r) tends to zero.

Self-review checked the real chain-rule factors, sphere norm, positive
annular radii, compact set domination, Hessian ordering, absence of a
conjugation in U, exact radius-squared mass scaling, and the limit squeeze.
This module does not assume or prove a Helmholtz moment ODE, angular
harmonic completeness, or exterior Rellich. Those are distinct steps.

Root independently read the complete final source at the recorded hash
and passed all 17 exports. Source frozen.

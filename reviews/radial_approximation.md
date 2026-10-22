# Independent audit of actual radial/reference comparison

Source: `lean/RadialApproximation.lean`.
SHA256: `F34F39613002663DB40FCCEC32DD3BD035BC64A0554D636E9A219781053C347D`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Compiler exit 0, no warnings, and all sixteen reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/RadialApproximation-independent-continuation.log`.

The actual radial state uses the explicit initial coefficients in the actual
Riccati-Bessel basis. Its initial value and actual ODE are proved using the
existing solution theorems. The state uses the product maximum norm, and the
literal generator estimate bounds both actual components. Gronwall gives the
actual norm bound, followed by a uniform bound on a fixed-width interval for
R at least one.

The difference equation with the actual constant reference is derived
algebraically. Its forcing is the actual angular term l(l+1)/(sigma*x^2),
bounded by l(l+1)/(sigma*R^2). A second Gronwall estimate yields the stated
O(R^-2) error times the initial-state norm, with the explicit exponential
constant. The actual fixed-width limit follows from that bound and only
convergence of the initial states; convergence of the propagated states is
not supplied as a premise. The state is also identified with the actual
previously constructed layer transfer matrix.

Scope: fixed degree l, fixed nonzero q, positive sigma, fixed nonnegative
width w, and R tending to infinity. Constants depend on l, q, sigma, and w.
This does not provide bounds uniform in growing angular degree or a varying
number/width of layers, nor a spatial Maxwell Green limit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 16 reports using only standard foundations. Final source SHA256 `f34f39613002663db40fccec32dd3bd035bc64a0554d636e9a219781053c347d`. Independent log: `lean/logs/RadialApproximation-independent-continuation.log`; log SHA256 `45cb442105ad67133ede8ab4e3fe398314466f1b95ee14d7328a7ede6576e2c2`. This certifies the stated scope, not either complete OQ14 construction.

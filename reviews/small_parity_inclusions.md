# Derived actual small-ball inverse for the explicit parity kernel

Source: `lean/SmallParityInclusions.lean`.

SHA256: `3F0FF8A42F14403CEB7E91303EE070DBFE0EDE0B91A4A917D5249CE132978097`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All five selected reports are standard-only. Importable
object: 398704 bytes.

For fixed enclosing radius R, fixed finite centers, nonnegative radius factor
rho, positive gain factor b, and a common nonnegative coefficient bound C,
the main theorem derives a positive delta. For every 0<a<delta and every
actual coefficient bounded by C and zero outside the literal radius-rho*a
balls, it constructs the actual support data and proves the explicit block
invertible with inverse norm at most two. No numeric operator-smallness
assumption remains in this theorem.

The volume bound uses the actual finite ball volumes. For V equal to the
sum of their fixed radius coefficients cubed times 4*pi/3, the derived
perturbation bound is bounded above by

`C*sqrt(V*a^3)*kernelSize(k,R) +
  9*C*V*entryBound(k)*(b^2*a + 2*a^3 + a^5/b^2)`.

This actual explicit expression is continuous and zero at a=0, giving the
threshold. The dynamic term retains the square-root-volume rate; it is not
the manuscript's sharper quadratic Schur estimate. The scaled parity
reaction terms have a genuinely derived vanishing bound despite gain b/a.

The coefficient's support and bound are actual material data. No static
isolated-sphere depolarization, response convergence, Maxwell equation for
the reaction field, finite-stack Green identification, shrinking-gap plane
estimate, or full channel result is assumed or concluded. Independent review
is pending.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 5 reports use standard foundations. Final source SHA256 `3f0ff8a42f14403ceb7e91303ee070dbfe0ede0b91a4a917d5249ce132978097`. Independent log: `lean/logs/SmallParityInclusions-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

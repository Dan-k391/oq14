# RadialIntervalUniqueness — actual finite-interval Cauchy uniqueness

Source: `lean/RadialIntervalUniqueness.lean`

SHA256: `E1E0C84F071DA387C210B65EAC28A5E7DCFB5490CE849E77786C09684523D710`

Evidence: `lean/logs/radial-interval-uniqueness-check.log`. Final compile
exited zero without warnings, created an importable object (204216 bytes),
and emitted five selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

For any open preconnected real domain and actual scalar solutions of
f'=df, df'=qf, the Wronskian numerator against another actual solution
has actual derivative zero. The mean value theorem on the connected
domain makes it independent of radius. If f and df vanish at one point,
the numerator is zero throughout the domain.

Given two actual basis solutions with a pointwise nonzero Wronskian,
their two zero numerators algebraically force both f and df to vanish.
The generic helper takes actual derivative certificates for those basis
solutions; it does not take an expansion or uniqueness premise.

The main physical radial specialization discharges all basis hypotheses
using the existing actual outgoing and incoming Riccati–Hankel solutions
and their exact Wronskian -2 I k. On Ioo R L with R>=0 and any nonzero
complex k, zero Cauchy data at an actual point r0 in the interval therefore
force f=df=0 on the entire interval. This includes the positive real
frequency case needed for continuation. No value or regularity at the
singular endpoint r=0 is assumed.

A two-solution version proves equality from equal Cauchy data. A
zero-neighborhood version derives the zero derivative at r0 from the
actual local equality f=0 and applies finite-interval uniqueness. The
interval need not be infinite and no asymptotic condition is used.

Self-review checked Wronskian signs, the two reconstruction identities,
derivative-zero connectedness, the open finite-interval domain, positive
radius exclusion of the pole, the exact nonzero complex-frequency
condition, and extraction of zero Cauchy data from neighborhood vanishing.
This uses the allowed actual Hankel basis route; it does not assert a
generic existence of a fundamental basis for arbitrary continuous q, nor
does it assume a PDE solution is analytic.

Root independently read the complete final source at the recorded hash
and passed all five exports. Source frozen.

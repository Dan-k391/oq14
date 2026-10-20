# Constructive route for exact static ball polarization

This is a proof-gap audit and proposed next construction, not a theorem.

The manuscript uses the exact isolated sphere identity at
`manuscript/sections/channel_transducer_limit.tex:241` through the leading
polarization discussion at line 252. The file hash at this audit is
`0C1C4D13DF2EFF9E344B8701B243E51FD83576C4408F68F28A5F0F16A2EBC487`.
The small-ball inverse and literal self-consistent relation now exist for
the explicit parity kernel; the exact sphere identity remains unproved.

The existing conventions fix the constants and signs:

- `lean/GreenKernel.lean:92` defines phi, with the off-origin value at k=0
  equal to `1/(4*pi*norm x)`. Hash:
  `721730A853CFF1A637C64B33326AC7742AD0F764CB2A93C4099C57CF07056642`.
- `lean/KernelSource.lean:110` proves its actual weak Helmholtz identity;
  at k=0 this is `Delta N = -delta_0`. Hash:
  `C7B394B39030743C227AE48DAC19154CAB28357231633E1696FE03880027C54A`.
- `lean/NewtonHessian.lean:36` defines the derived Hessian symbol as
  `-xi_i*xi_j/norm(xi)^2`. Hash:
  `A6719B49C0F35E32AA080DFFDFE194C7722054F61C3E3622582DB23BF6415244`.
- `lean/NewtonL2.lean:219` defines the actual Newton operator as minus the
  actual physical longitudinal projection. Hash:
  `9681B67130FF86461C375D501030E3AA8442CB9D26321BB94F7E84F9CA39EDB4`.
- `lean/NewtonL1L2.lean:115` proves literal spatial Newton-Hessian pairings
  for actual integrable L2 sources. Hash:
  `0C44B76BE988E07FE4E816AA074DE7414CC69593B3D71D4DED627952F7C5D51A`.

For R>0 define the actual radial scalar potential

`Psi_R(x) = R^2/2 - norm(x)^2/6` when norm(x) <= R,
and `R^3/(3*norm(x))` outside.

The two values at R equal R^2/3. Their radial derivatives both equal -R/3.
The interior is a polynomial, so the origin is regular. Proving actual C1
matching, followed by weak integration by parts, should give the global
identity `-Delta Psi_R = indicator(ball 0 R)`, with no interface delta.
The explicit Hessian is `-delta_ij/3` inside, and
`(R^3/3)*(3*x_i*x_j/r^5-delta_ij/r^3)` outside.

The next exact target is a genuine L2 constant-ball source F_R,P and an AE
equality between `NewtonL2.newtonOperator F_R,P` and this explicit Hessian
contracted with P. Its interior value is then -P/3. Translation gives the
same result for balls at arbitrary actual centers, and linearity handles a
finite collection without assuming away interactions.

One genuine identification step is still needed after the explicit weak
PDE: either prove Psi_R is the literal convolution N*indicator(ball), or
prove a global L2 weak div/curl characterization of the already constructed
physical projection. The latter can use the explicit gradient and Hessian,
which are globally L2 (tails r^-2 and r^-3). Psi_R itself is not globally L2,
so it must not be placed in that space. Actual weak-derivative Fourier
identification or proved H1 gradient density would discharge the Hodge
uniqueness step.

`lean/GradientProjection.lean:74` and line 115 currently give the corresponding
projection properties for Schwartz gradients and divergence-free Schwartz
fields. They do not provide that general L2 characterization. Hash:
`65D95EB77E0DAC88C599E6E3C5A66DC89F82B5B7C1C44F0EE7AFFB7E2221C960`.
Consequently the desired -P/3 identity cannot be imported from the existing
interfaces or treated as a premise. The suggested construction must prove
this identification before deriving the manuscript's isolated-sphere
polarizability factor 3/(epsilon+2).

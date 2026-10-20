# RadialIntervalFlux — actual finite-interval moment and flux uniqueness

Source: `lean/RadialIntervalFlux.lean`

SHA256: `F2AE3587AE6F4D5AC199E6CE4E95817DDBABA7085934880D1B30E82F13AAF0EC`

Evidence: `lean/logs/radial-interval-flux-check.log`. Final compile exited
zero without warnings, created an importable object (122352 bytes), and
emitted four selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The hypotheses are actual U'=F/r^2 and
F'=(l(l+1)-k^2 r^2)U on Ioo R L, with R>=0 and complex k nonzero.
The existing proved derivative transformations f=rU and df=U+F/r give
the actual finite-interval radial equation. The audited finite-interval
radial uniqueness theorem then propagates zero Cauchy data. Since every
interior radius is positive, f=df=0 implies both U=0 and F=0.

The zero-neighborhood theorem needs only U=0 on a neighborhood of one
actual interior radius. Multiplication gives f=0 on that neighborhood;
the actual finite-interval derivative equation supplies the missing zero
derivative. Hence both U and F vanish throughout the interval. A final
two-pair version derives uniqueness from equality of U and F at one
radius by applying the homogeneous result to their difference.

Self-review checked the actual flux derivative premises, complex radius
embeddings, exclusion of r=0, recovery of both U and F, neighborhood
vanishing without an extra F=0 hypothesis, and the two-pair difference
equations. No annular Green identity, PDE analyticity, arbitrary moment
ODE, or zero-propagation premise is silently introduced.

Root independently read the complete final source at the recorded hash
and passed all four exports. Source frozen.

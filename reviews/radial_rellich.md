# RadialRellich — actual radial ODE basis and nondecay

Source: `lean/RadialRellich.lean`

SHA256: `775A2375FD3E936C550B9A5DA7BC22182D49D2A58E8681D93A168E5B74E29B04`

Evidence: `lean/logs/radial-rellich-check.log`. All 20 selected exports
compiled cleanly with an importable object and only `propext`,
`Classical.choice`, and `Quot.sound`.

For any two scalar solutions of f'' = qf on an open real half-line, the
actual Wronskian numerator has derivative zero. If two given actual
solutions have a fixed nonzero Wronskian, the variation coefficients for
every third solution are differentiated and shown independent of radius
by the connected open-interval mean value theorem. Their two-solution
expansion is therefore derived rather than assumed.

The actual all-degree factorial-series Riccati--Hankel functions are
composed with the radius, with both first and second real derivatives
proved from their complex derivatives. Their radial equation is
f'' = (l(l+1)/r squared - k squared) f, and their exact radial Wronskian is
minus two i k. These supply the required two-solution basis for every
fixed natural degree and nonzero complex frequency.

At positive real frequency, the inverse-radius polynomials tend to one.
After removal of the outgoing exponential phase, a general combination has
the leading form a times (-i) to power l+1 plus b times i to power l+1
times exp(-2ikr). The remainder tends to zero. A shift by pi/(2k) reverses
the second phase. If that leading expression tends to zero, adding its
shifted version forces the first coefficient to vanish; its norm then
forces the second coefficient to vanish.

The final export states that an actual solution of the displayed radial
equation whose Riccati amplitude tends to zero must vanish on the entire
exterior half-line. It accepts actual first-derivative equations for f and
its derivative representative. It does not accept a presumed Hankel
expansion, radiation uniqueness, or exterior Rellich theorem.

Self-review checked the real chain-rule factors, radial curvature
rescaling, exact Wronskian sign and nonzero hypotheses, connected half-line
coefficient argument, the finite inverse-polynomial limit, real phase norm,
half-period identity, oscillation cancellation, and transfer from eventual
asymptotics to equality on the entire half-line.

Scope: this is the radial component of the proposed actual exterior Rellich
proof. The actual annular Green identity and harmonic-polynomial moments
must still supply its radial ODE and vanishing-amplitude premise. Harmonic
polynomial decomposition and sphere density must then convert zero moments
to a zero exterior field. Those steps are not asserted here. Root
independently read the complete final source at the recorded hash and
passed all 20 exports. The source is frozen.

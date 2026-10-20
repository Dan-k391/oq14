# RadialMomentODE — actual flux pair to zero moment

Source: `lean/RadialMomentODE.lean`

SHA256: `B800B8771D3ACDAFB78FD5F963A53012037056B541F28B55913DCB12C894B8DE`

Evidence: `lean/logs/radial-moment-ode-check.log`. Final compile exited
zero without warnings, created an importable object (284168 bytes), and
emitted four selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The algebraic hypotheses are explicit actual derivative identities:
U'=F/r^2 and F'=(l(l+1)-k^2 r^2)U. The Riccati representative is f=r U;
its derivative representative is U+F/r. Product and quotient derivative
rules give f'=U+F/r and f''=(l(l+1)/r^2-k^2)f whenever r is nonzero.
No Hankel expansion or second derivative equation is assumed separately.

On an exterior half-line R>=0 and for actual positive real k, the existing
RadialRellich theorem then shows that rU tending to zero forces U=0 at
every radius r>R. The actual moment specialization imports the proved
RadialMoment differentiation and mass decay results. It leaves exactly
two flux facts for the annular Green step to prove: equality of momentD
with F/r^2 and the stated actual derivative of F.

Self-review checked complex embeddings of r, quotient derivatives,
cancellation of F/r^2 terms, the radial coefficient, the positive-radius
division, the exact positive-real frequency premise, and use of actual
spherical squared mass rather than an assumed radial decay theorem.
This module does not claim the unresolved annular Green identity.

Root independently read the complete final source at the recorded hash
and passed all four exports. Source frozen.

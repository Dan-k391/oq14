# OneDimensionalGreen — actual local integration by parts and fundamental lemma

Source: `lean/OneDimensionalGreen.lean`

SHA256: `6B37503AB59B24351FA22CB068847BA02C403A98A4078DDC6757C35B81C625F8`

Evidence: `lean/logs/one-dimensional-green-check.log`. Final compile exited
zero without warnings, created an importable object (266216 bytes), and
emitted eleven selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The domain is any actual open subset Omega of the real line. For a local
coefficient a and a compact smooth test psi whose topological support is
contained in Omega, their product is globally continuous and integrable.
It also has a global actual derivative: inside Omega the product rule
applies, and outside Omega the test is identically zero on a neighborhood.
The support of its derivative stays in the same compact test support.
Thus the actual integral of the derivative vanishes, proving integration
by parts. Repeating this gives the genuine second-derivative identity.

The general Green identity is integral(a psi''+b psi'+c psi) equal to
integral((a''-b'+c) psi), with actual derivative representatives and
continuous highest derivatives. A real-test specialization carefully
embeds eta, eta', and eta'' into the complex numbers. It does not impose
complex smoothness on the field coefficients or identify real and complex
derivatives.

For a continuous complex residual on Omega, the pinned actual
AEEqOfIntegralContDiff fundamental lemma implies zero almost everywhere
from its integrals against every real C-infinity compact supported test.
The open-set continuous AE equality theorem then proves zero at every
point. No test-separation or pointwise equation premise is added.

The final `weak_green_pointwise` theorem accepts actual a'=da, da'=dda,
b'=db and continuous dda, db, c; it derives dda-db+c=0 everywhere in Omega.
The direct `weak_green_pointwise_deriv` interface accepts a C2, b C1, and
c continuous on Omega, and concludes deriv(deriv a)-deriv b+c=0 from the
same actual compact-test identity. Setting Omega=Ioi R is immediate.

Self-review checked local support at the material boundary, compact
integrability of every separated term, both integration-by-parts signs,
the derivative support closure, real-test embeddings, local integrability
in the fundamental lemma, and the continuity upgrade. This module does
not assert the still separate spatial annular Green identity or a
Helmholtz moment equation before its weak integral identity is proved.

Root independently read the complete final source at the recorded hash
and passed all eleven exports. Source frozen.

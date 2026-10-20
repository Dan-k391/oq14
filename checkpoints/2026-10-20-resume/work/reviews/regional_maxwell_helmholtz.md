# RegionalMaxwellHelmholtz — actual weak Maxwell to scalar Helmholtz

Source: `lean/RegionalMaxwellHelmholtz.lean`

SHA256: `60E8A6B30B193D75365A73B98CF4865EFFB3031C4E45250990716FC056F6F9B5`

Evidence: `lean/logs/regional-maxwell-helmholtz-check.log`. Final compile
exited zero without warnings, created an importable object (540256 bytes),
and emitted twenty-two selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

Regional tests are literal complex C-infinity compact functions with
topological support inside the region. Actual coordinate derivatives
preserve this test class by the genuine Frechet derivative support
theorem, and second derivatives commute by actual smooth calculus.
These identities give divergence of weak curl equal to zero and weak
curl-curl equal to the gradient-divergence term minus the component
Laplacian pairing. No field Gauss or Helmholtz identity is assumed.

The actual Maxwell test equations use curl E=I k H and
curl H=-I k epsilon E for real constant epsilon. Nonzero k derives weak
div H=0; nonzero epsilon additionally derives weak div E=0. Applying the
two actual curl equations again gives the component Laplacian identity
with coefficient k^2 epsilon. All pairings are bilinear without complex
conjugation, consistent with the existing actual Maxwell test convention.

Integrability of the finite separated test terms is explicit and is
derived either from actual component local integrability or from actual
region L2 classes. The exact identity
(k sqrt(epsilon))^2=k^2 epsilon for positive epsilon then gives the exact
WeakHelmholtzRegularity.IsWeakHelmholtz predicate for each E/H component.

The final actual-domain exports accept existing DomainCurl.HCurl fields
and WeakConservation.WeakMaxwell with permeability one and constant
positive permittivity. Genuine compact C1 regional curl tests receive the
smooth test functions; restricted-measure curl equations are transferred
to whole-space integrals because tests vanish outside the region.
Actual regional L2 test integrability discharges every technical
integrability premise. No global L2 property, field differentiability,
boundary condition, or smooth field representative is required.

Self-review checked weak curl signs, both derivative commutations,
divergence cancellation, nonzero scalar divisions, k^2 epsilon sign,
finite integral exchange, the material frequency square, zero outside
test support, actual restricted-to-global integral equality, and the
existing HCurl/Maxwell interface. The module derives weak scalar
Helmholtz only; regularization and continuation remain separate.

Source frozen pending root independent mathematical audit.

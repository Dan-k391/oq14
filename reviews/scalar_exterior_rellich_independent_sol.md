# Independent Sol audit of actual exterior scalar Rellich uniqueness

Source: `lean/ScalarExteriorRellich.lean`.

Audited SHA256: `239708022D890544E618C3CACE2BF6D9A3E90D1FD099A31A4D4AF76009ABA9A2`.

Independent full-source mathematical audit: PASS. Independent pinned Lean 4.19 compilation: exit 0, no warnings, three dependency reports containing only `propext`, `Classical.choice`, and `Quot.sound`, on 2026-10-20. The source was not edited.

The actual spatial Helmholtz equation and exterior smoothness first supply the literal weak spherical moment equation. The genuine one-dimensional classical moment theorem then derives both actual radial flux identities. These identities are conclusions of the PDE argument, rather than independent assumptions.

At positive real frequency, the proved radial Rellich theorem applies to these actual moments. The actual spherical mass limit, whose definition contains radius squared times the actual angular squared modulus, gives decay of radius times each moment by the proved integral inequality. The genuine radial ODE uniqueness result therefore annihilates every actual homogeneous harmonic moment on every exterior sphere.

The literal harmonic polynomial restriction agrees with the actual angular polynomial used in those moments. The proved continuous harmonic moment separation theorem forces the actual field to vanish at every point on each exterior sphere. Finally the actual normalization of each nonzero exterior point to a unit sphere point gives pointwise exterior vanishing.

The final theorem assumes only nonnegative exterior radius, positive real frequency, actual exterior smoothness, the actual classical Helmholtz equation, and decay of the literal spherical mass. There is no spherical completeness, outgoing uniqueness, flux identity, modal field equation, or Rellich conclusion inserted into the hypotheses.

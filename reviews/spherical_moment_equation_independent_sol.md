# Independent Sol audit of the actual spherical moment weak equation

Source: `lean/SphericalMomentEquation.lean`.

Audited SHA256: `C23EA85E25BB4D6D185650F99FB179FAA8E9110A10D717735D1F93E7623F68D2`.

Independent full-source mathematical audit: PASS. Independent pinned Lean 4.19 compilation: exit 0, no warnings, nine dependency reports containing only `propext`, `Classical.choice`, and `Quot.sound`, on 2026-10-20. The source was not edited.

The test is the actual product of a smooth compactly supported radial profile eta of the norm and the literal complex evaluation of a real homogeneous harmonic polynomial. Its global smoothness, compact support, and exterior support are genuinely established. The exact actual Laplacian uses the proved homogeneous Euler identity and harmonicity, giving eta double-prime plus (twice the degree plus two) eta prime divided by radius.

The actual local Helmholtz equation gives the true compact-test weak spatial identity, with integrability proved by localization. The genuine complex polar formula transforms it to an angular integral; actual polynomial homogeneity supplies radius to the degree and the actual Jacobian supplies radius squared. This yields the literal weighted spherical moment equation, without a modal field-equation premise.

The polynomial form removes division only at positive radii, where the radius is nonzero. Extending the integral to the whole real line is justified because the profile and both actual derivatives vanish on neighborhoods of every nonpositive radius, using exterior radial support and the nonnegative exterior radius. Real-profile complexification preserves actual support and the first two derivatives. Thus the final real-test identity is suitable for the genuine one-dimensional weak-to-classical theorem, with no hidden integrability, flux, or radial ODE premise.

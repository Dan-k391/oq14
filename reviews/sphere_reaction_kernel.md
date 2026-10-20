# Explicit sphere-integral parity kernels

Source: `lean/SphereReactionKernel.lean`.

SHA256: `084F2BAA0BF822258BD6C5658BE3624F981A697309FA29E766AED04157A6B5CE`.

Author pinned Lean 4.19 compiler and object emission completed with exit 0,
without warnings. All 12 selected reports are standard-only. Importable
object: 309224 bytes.

The source defines the actual unit-sphere surface measure as the Haar polar
measure `volume.toSphere`. It defines J entrywise by
`k^3/(16*pi^2) * integral ((delta_ij-theta_i*theta_j)*exp(i*k*theta.dot(x)))`.
The integral is genuinely integrable, continuous in x, and uniformly bounded
by `abs(k^3/(16*pi^2))*2*surfaceMass`. Each sphere coordinate has norm at
most one and the oscillatory exponential has norm exactly one.

Reflection negates the third spatial coordinate. The literal reaction
kernel is `i/2` times J(x-y) minus the reflected output row for electric-wall
parity, and plus that row for opposite-wall parity. The reflected row has
the sign of the corresponding R_z diagonal entry. Both actual two-point
kernels are continuous and have the same uniform entry bound as J.

This constructs and estimates the explicit Herglotz kernels. It does not
claim equality with a finite radial-background Green kernel, equality with
the imaginary part of the free dyadic, distributional Maxwell equations,
all spatial derivatives, or a far-field expansion. Those are separate
constructions. Root independently read the complete source and checked all
12 reports with the pinned compiler: PASS. Root requested a comment-only
clarification of the Boolean wall signs; the hash above includes that
clarification, and author recompilation at that hash again passed all 12
reports without warnings. No mathematical definition or proof changed.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 12 reports use standard foundations. Final source SHA256 `084f2baa0bf822258bd6c5658be3624f981a697309fa29e766aed04157a6b5ce`. Independent log: `lean/logs/SphereReactionKernel-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

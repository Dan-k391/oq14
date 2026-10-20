# Classical exterior Maxwell equations

`lean/ExteriorClassical.lean` is frozen with 18 checked exports.

SHA256: `410a3d34e158423e66a598957d3522f1f11de0a84ab80c8a5af1a6b2d009901c`.

For a componentwise L1 complex vector source supported in a fixed closed ball, the final theorem proves `MaxwellAt k 1 1` for the actual ordinary exterior electric dyadic integral and magnetic gradient integral. For every nonzero real frequency it also proves both classical Gauss laws, `div E = div H = 0`.

The proof identifies the actual scalar potential `A` from the outgoing scalar kernel. The previously proved first and second derivatives of that literal source integral give

- `E = k² A + grad(div A)`;
- `H = −i k curl A`.

All equalities hold throughout the exterior open set. The file proves local mixed-partial symmetry, curl-gradient zero, and curl-curl equals gradient-divergence minus componentwise Laplacian from actual real Fréchet derivatives. Its input regularity is discharged by `ExteriorSmooth`, and its componentwise Helmholtz equations are discharged by `ScalarExteriorSecond`. Eventual equality on a neighborhood transfers actual derivatives to the original integral representatives. The Gauss proof differentiates the local Maxwell identities and uses nonzero frequency explicitly.

No source smoothness, global field regularity, exterior Maxwell equation, or derivative-under-integral conclusion is an assumption of the final source-response theorem. The intermediate potential calculus theorem accepts actual scalar Helmholtz equations, which the final theorem proves from the source integral. This is a source-response result, not a uniqueness or Fredholm solvability theorem for an arbitrary dielectric.

`lean/exterior-classical-verification.txt` contains the complete direct compiler output. `lean/exterior-classical-provenance.json` records the exact compiler, locked package metadata, recursively imported local source hashes, and log provenance. Direct compilation and olean generation both returned exit code 0; all 18 selected exports use only `propext`, `Classical.choice`, and `Quot.sound`. This source-scoped check uses the existing pinned dependency build; the coordinator owns the separate clean aggregate rebuild.

The coordinator's independent complete source audit passed. Peer review was requested.

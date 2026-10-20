# Axial volume coordinates

Author verification for `lean/AxialCoordinates.lean`.

- Source SHA256: `4E03176585805C595AA06A19745CED5FDC0246E69C62D4161D39523114C81147`.
- Pinned Lean 4.19.0 final compilation and object emission: exit 0, no warnings; object 924528 bytes; all thirteen reports contain only `propext`, `Classical.choice`, `Quot.sound`.
- Exact log: `lean/AxialCoordinates.final.log`, SHA256 `93AABCE89D53032F7643DFF922DF46472D467ABD3A2B89F84EAA16A04C1EE2E6`.

The actual map from radius, latitude, and azimuth is `(r*sqrt(1-z^2)*cos(theta), r*sqrt(1-z^2)*sin(theta), r*z)`. It acts on the genuine three-coordinate real function space with its actual product volume. The Euclidean L2 norm of its physical vector is proved to be the radius on the stated positive-radius domain. The displayed continuous linear derivative and its determinant `-r^2` are proved from actual differentiation and finite matrix algebra.

Injectivity recovers radius from the Euclidean norm, latitude from the third coordinate, and azimuth from the existing actual planar polar homeomorphism. The image contains every point whose transverse coordinate of index 1 is nonzero. Its complement lies in the actual kernel of this coordinate projection, a null proper subspace. Thus the actual image covers Euclidean product volume almost everywhere.

The nonnegative and real change-of-variables formulas follow from the proved Jacobian, injection, measurable open domain, and actual image coverage. No spherical measure identity is assumed. That angular identity remains the next measure-cone/Fubini step.

Independent root full-source and compiler audits requested. Source held stable.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 13 reports use standard foundations. Final source SHA256 `4e03176585805c595aa06a19745ced5fdc0246e69c62d4161d39523114c81147`. Independent log: `lean/logs/AxialCoordinates-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.

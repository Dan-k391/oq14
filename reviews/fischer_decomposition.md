# FischerDecomposition verification

Source: `lean/FischerDecomposition.lean`.
SHA256: `4D37CEAE3E494724C3B09BC2F99505501E6E25DA4A7D93EA3CDCE9A87C064108`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All 11 selected theorem dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

For each degree n, the Fischer submodule is the actual finite real linear
span of radiusSq^j*h with h homogeneous harmonic and degree(h)+2j=n.
Positive explicit Laplacian radial coefficients give actual polynomial
preimages of every generator in degree n-2. Span induction extends the
preimage construction to that full submodule. Strong degree induction
subtracts such a preimage from any homogeneous polynomial, leaving a
harmonic polynomial. The low-degree cases follow because their first
partials are constant.

On the unit sphere the actual radiusSq polynomial evaluates to one.
Consequently each homogeneous polynomial restriction belongs to the finite
span of homogeneous harmonic restrictions. Summing actual homogeneous
components proves this for every polynomial. Frozen SpherePolynomial
density then proves harmonicSpan_dense in the uniform topology.

The actual evaluation scaling formula is proved monomial by monomial from
homogeneous degrees, for every real scaling parameter. Its complex version
and the concrete actual spatial Laplacian-zero bridge supply the smooth
homogeneous harmonic functions used by the exterior moment argument.

Independent full-source review requested from root at this hash.

Root completed the independent full-source audit at this hash. Final freeze PASS.

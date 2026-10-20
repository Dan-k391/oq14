# Actual volume solvability conditional on homogeneous uniqueness

Source: `lean/VolumeAlternative.lean`.

SHA256: `F3963544D87812FCEAF42F51AB3DEBBBF3D0ADBA25D5E380F9C831703CA32486`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). All eight theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full-source audit passed, including the homogeneous-uniqueness scope and inverse range transfer. The source is frozen at the hash above.

The homogeneous uniqueness premise is stated literally as: for every vector L2 field u, if the actual dynamic volume block applied to u is zero, then u is zero. This gives injectivity of both the actual and preconditioned blocks. The genuine compact-operator alternative then gives preconditioned surjectivity; multiplication by the proved static inverse transfers it to the actual block. Bijectivity and the Banach inverse theorem yield an actual bounded linear inverse. Both inverse identities and unique solvability for every vector L2 right-hand side are exported. The orthogonal-kernel bound gives an existential positive uniform solution estimate once the kernel is trivial.

The file assumes neither final surjectivity nor an inverse. It has no volume or contrast smallness condition. Homogeneous uniqueness is an explicit remaining input, so this establishes the arbitrary-size Fredholm reduction and conditional volume solvability, not unconditional outgoing Maxwell uniqueness or a complex-frequency analytic Fredholm theorem.

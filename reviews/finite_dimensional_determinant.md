# Actual analytic determinant in finite dimensions

Source: `lean/FiniteDimensionalDeterminant.lean`.

SHA256: `7FA4B30F0FB5EDB256D0D0699C42585F8E3A7E25F919512A43329D7D333B3544`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All three exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full-source audit passed at this exact hash. The source is frozen.

Continuous basis-coordinate maps evaluate the actual analytic endomorphism family. The finite Leibniz determinant formula proves actual scalar determinant analyticity. Algebra equivalences identify continuous endomorphisms, linear endomorphisms and matrices; the matrix determinant criterion proves that the actual finite-dimensional continuous endomorphism is a unit exactly when its determinant is nonzero.

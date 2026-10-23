# Differentiation of the actual vector reaction series

`lean/VectorReactionSeries.lean`: three author-final reports, exit0, no
warnings, standard foundations only. Independent audit pending.

The literal normalized physical vector mode series is defined by its
actual scalar coefficient and differentiated Maxwell dyads. A summable
uniform bound for every derivative through the chosen order proves
derivative summability, equality with the actual derivative of the sum,
and uniform convergence of the derivative partial sums on a compactly
controlled core ball. The proof uses the genuine local smooth-series
theorem, not an assumed derivative interchange. The N+2 scalar control
radius accounts for both Maxwell curls. Origins are included.

This is still a series theorem; full outgoing point-source Green
identification is a separate requirement.

Source SHA256 `60f66409d851348453c4b613b8cd9c71f44f5d3efdeac14993f600dd1ce39abd`.
Final log `lean/logs/VectorReactionSeries-final.log`, SHA256
`b527149e120e193b4f7f90950370c4a81f4c832e0bcacb0046d3f5b26f37242c`.

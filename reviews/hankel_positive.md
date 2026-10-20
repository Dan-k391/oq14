# Hankel positivity independent audit

Independent whole-source mathematical review and pinned compiler recheck by `fredholm_sol`: PASS.

- Source: `lean/HankelPositive.lean`.
- Exact SHA256: `3C0111A4DD239CBB6623309B38A3007B8D98CA7B5477F4FF1D238D4A3AD1833A`.
- Pinned Lean 4.19.0 independent `lake env lean HankelPositive.lean`: exit 0, no warnings; all seven reports contain only `propext`, `Classical.choice`, `Quot.sound`.
- Log: `lean/HankelPositive.independent-fredholm.log`, SHA256 `CB77FD9CE497B0C37015198CACDA56DBA66E2A3714EFE961EDB0F663CB88F586`.

For real inverse coordinate, the opposite-phase finite polynomial is proved to be the complex conjugate. Its actual product is therefore the literal squared norm of the finite Hankel factor and hence of the actual real-frequency outgoing function. Nonnegative real coefficients give nonnegative real derivative evaluation for nonnegative inverse coordinate.

The chain rule through `1/r` gives the actual squared-norm derivative `-P'(1/r)/r^2`. Comparing it with the already proved actual derivative `2*radialLoad(xi,xiD)` establishes the nonpositive outgoing radial load at every positive radius and every degree. The sign, polynomial identity, and derivative are proved, not included in the input. Degree zero is covered and gives zero load.

Frozen source unchanged.

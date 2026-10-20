# Actual Taylor coefficients of analytic finite-dimensional factorizations

Source: `lean/FiniteRankAnalyticJets.lean`.

SHA256: `8C084403517571A644D9624EBC5E80794E2E83C184227C5037A5FB7CAA6F3F93`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All six exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final complete-source audit passed at this exact hash. The source is frozen.

Composition through a fixed finite-dimensional space has finite-dimensional range, and finite-dimensional ranges are preserved under finite addition. For analytic operator factors A and B, the actual derivative of their composition satisfies the local Leibniz formula. Induction, equality of actual derivative germs, and the iterated derivative sum theorem prove that every actual Taylor jet of A(z) composed with B(z) has finite-dimensional range.

The actual power-series coefficient is proved equal to the corresponding iterated derivative divided by its factorial, using the established factorial derivative theorem. Scalar multiplication preserves the finite range. This proves finite rank of the actual analytic power-series coefficients; no assertion that pointwise finite rank alone passes to derivatives is used.

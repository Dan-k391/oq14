# Actual anchored analytic compact inverse

Source: `lean/AnalyticCompactInverse.lean`.

SHA256: `8855F4647BA7B9D9C6A6331068696047EC40979E054E180EC5F96896E581CE72`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. Both exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final full-source audit passed at this exact hash. The source is frozen.

At every center, actual finite-rank approximation supplies a fixed finite-dimensional Schur reduction. The analytic regular inverse and the actual finite-dimensional meromorphic inverse are combined through proved bounded-bilinear composition and addition. The exact Woodbury identity identifies this meromorphic function with the actual inverse of identity minus the original compact family on a punctured neighborhood. Punctured invertibility is supplied by the previously proved anchored global theorem, rather than assumed.

The result is genuine operator-valued meromorphy of the actual inverse on the whole complex plane for every entire compact Hilbert-operator family with one actual unit value. Finite rank of its principal Laurent coefficients is a separate further result.

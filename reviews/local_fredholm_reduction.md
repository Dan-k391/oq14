# Genuine local determinant reduction and anchored global discreteness

Source: `lean/LocalFredholmReduction.lean`.

SHA256: `19A15E97381EFA1338F09C69A0ECCAD7FF016979C2FC9DE95473B3268ACCFE8B`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All sixteen exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final full-source audit passed at this exact hash. The source is frozen.

A fixed finite-rank approximation F=I B to the actual compact operator at a parameter center gives an open neighborhood where the residual norm is below one. The regular factor A=1-(T-F) is actually invertible there by the Neumann series. Its inverse is analytic. The actual reduced map D=1-B A-inverse I is analytic on that neighborhood. The proved Schur identities identify invertibility of 1-T with invertibility of D and give the actual Woodbury inverse.

For finite-dimensional auxiliary space, the actual analytic determinant and exact unit criterion give the local alternative: either all nearby operators are singular or every sufficiently near punctured parameter is invertible. Actual compact approximation supplies such a reduction at every parameter center. The proved connected-propagation lemma and one actual invertible basepoint exclude the all-singular branch globally. Thus every complex center has a punctured neighborhood of invertibility. The exceptional set is also closed.

No local finite-rank approximation, local Schur invertibility, global exceptional discreteness, or operator holomorphy conclusion is assumed. The meromorphic inverse and finite rank of principal Laurent coefficients are separate conclusions beyond this module.

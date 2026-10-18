# Actual TM matching inverse and nonzero simple-pole residue

Source: `lean/ModalMatching.lean`; namespace `OQ14.ModalMatching`.

The module constructs a two-amplitude linear matching map directly from the actual finite-series functions. Its rows are `n*psi(n*z)*a - xi(z)*b` and `psiD(n*z)*a - xiD(z)*b`. The determinant is the negative of the previously defined actual TM determinant; the explicit inverse uses the corresponding sign-correct adjugate divided by that determinant.

Both inverse identities are proved algebraically. The actual all-degree Hankel Wronskian proves that the outgoing boundary state `(xi,xiD)` is nonzero. This discharges the otherwise necessary rank condition and proves that the determinant vanishes exactly when the constructed matching map has a nonzero kernel.

The existing actual second-derivative formulas give the regular-function second derivative and differentiability of the actual determinant. At a nonzero simple determinant zero, the derivative-as-slope theorem gives the actual punctured-neighborhood limit `(z-z0)/D(z) -> 1/D'(z0)`. The same slope limit proves that the determinant is nonzero throughout a sufficiently small punctured neighborhood. Thus the inverse genuinely exists there.

Continuity of the actual adjugate entries proves the corresponding inverse-map residue limit on every forcing vector. The residue maps into the matching kernel, is nonzero on at least one explicit coordinate forcing, and its image factors through an explicit nonzero complex vector. The factorization is proved in both cases `xiD=0` and `xiD!=0`; it proves that the image is a nonzero complex line, rather than only proving that a determinant is zero.

The final theorem combines these proved statements with `ModalAsymptotics`. For each fixed angular degree and every real refractive index n>1, it constructs actual inverse matching-map poles below the real axis with an arbitrarily large positive frequency-to-decay ratio and a nonzero matching-kernel residue. It has no determinant-zero, simplicity, matching-solvability, or pole-existence premise.

This is an actual finite-dimensional boundary-amplitude inverse, not yet a theorem identifying the infinite-dimensional Maxwell resolvent. Full vector-field construction, regularity at the origin, actual interface-trace identification, outgoing Fredholm equivalence, and separation from all other angular degrees remain separate formal obligations. No such equivalence is assumed here.

Self-audit checked the determinant sign, both inverse identities, all cases of outgoing-state nonvanishing, derivative normalization in the residue, punctured-neighborhood invertibility, both explicit rank-one cases, and the final unconditional existence instantiation. All 16 qualified theorem exports compile with only standard axioms, without lints or proof placeholders. Evidence: `lean/logs/modal-matching-check.log`.

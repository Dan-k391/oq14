# Positive static inverse and polarization residual formalization

Source: `lean/StaticVolume.lean`, ten audited declarations.

The operator is concretely `1 + S.adjoint.comp (P.comp S)` on a complete
complex Hilbert space. Positivity of P implies its real quadratic form
is at least the squared norm, hence its norm lower bound. The pinned
mathlib coercive-operator theorem gives an actual unit, and evaluating
the inverse identity proves inverse norm at most one.

For a perturbation Q of norm below one, the proof factors
`A-Q = A (1-A^-1 Q)` and proves the normalized perturbation norm is below
one. The actual convergent geometric-series unit supplies invertibility.
The norm lower bound yields inverse norm at most `1/(1-norm Q)`. Applying
that inequality to u-v proves the error bound from the literal residual
`f-(A-Q)v`, whenever `(A-Q)u=f`.

The source also derives positivity of an actual closed-subspace orthogonal
projection using its proved adjoint identity, and specializes the inverse
bound to its weighted block. It does not assume an operator named Maxwell
has the required identification. Construction/identification of the
physical longitudinal projection and Newton kernel is still separate.

Root wrote the module and checked its ten axiom reports. The channel agent
independently read the entire source and found no defect in coercivity,
invertibility, factorization, quantitative constants, or residual identity.
The successful direct compiler run used Lean4.19 and reported only
propext, Classical.choice, and Quot.sound for all ten exports. The combined
clean source build supplies reproducible source hashes and raw evidence.

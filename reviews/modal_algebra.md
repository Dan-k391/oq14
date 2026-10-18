# Modal determinant algebra checked in Lean

Source: `lean/ModalAlgebra.lean`. Namespace: `OQ14.ModalAlgebra`.

The file defines the finite spherical Riccati-Hankel Laurent polynomials from their factorial coefficients, including their first and second derivatives. Their derivative theorems use actual complex `HasDerivAt` and finite sums of integer powers; derivatives are not arbitrary symbolic fields.

The outgoing and incoming Riccati expressions are defined by those polynomials times their exact complex exponential and phase factors. Their actual derivatives and the derivative of their half-sum are proved. The TM determinant is then the exact expression from the manuscript, `n*psi(n*z)*xi'(z)-xi(z)*psi'(n*z)`.

The following are checked without a pole-simplicity hypothesis:

- `tmDet_exp_factorization`: the exact exponential two-term factorization, including its nonzero prefactor.
- `tmDet_zero_iff_exp`: at a nonzero plus coefficient, exact equivalence of a determinant zero and `exp(2*i*n*z)=-Cminus/Cplus`.
- `matching_pair_not_both_zero`: the nonzero interior-Wronskian algebra that excludes simultaneous zero matching coefficients.
- `multiple_tm_zero_forces_rational_derivative`: a zero of the actual TM determinant together with a zero of its actual complex derivative forces the rational derivative condition `R'(z)=2*i*n*R(z)`. Differentiability of both Laurent coefficients is proved; the desired derivative condition is not an assumption.
- `l_one_wronskian`: direct evaluation of the actual degree-one finite expressions gives the exact Wronskian `-2*i`.
- `l_one_coefficients_not_both_zero` and `l_one_plus_ne_zero_at_pole`: the degree-one coefficient nonvanishing follows from that explicit Wronskian, rather than being supplied as a pole hypothesis.
- `l_one_multiple_zero_rational_condition`: both the rational pole equation and the rational derivative equation for a hypothetical multiple degree-one pole, with only nonzero n, nonzero z, and actual determinant/derivative zero hypotheses.

The generic matching-pair lemma is not presented as a proof of the general-degree Hankel Wronskian. That Wronskian is evaluated explicitly only for degree one in this module. The definitions use the known finite Riccati-Hankel expressions; identification with any separately defined special-function Bessel API is not formalized. The Lindemann-Weierstrass transcendence step, generic rational-function algebraicity and separation, analytic Fredholm theory, pole existence and the complete modal device construction remain mathematical manuscript proofs, not claimed Lean consequences of this file.

The file includes axiom reports for its principal theorems. No `sorry`, `admit`, or new axiom is used. This is an additional exact analytic/algebraic bridge; it does not make the full continuum proof a Lean theorem.

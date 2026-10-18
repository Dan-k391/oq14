# Actual algebraicity of exceptional modal roots

Source: `lean/ModalAlgebraicity.lean`; namespace `OQ14.ModalAlgebraicity`.

This module supplies the algebraicity step left separate by the frozen determinant, general Wronskian and rational-polynomial modules. It uses the actual subalgebra `Subalgebra.algebraicClosure ℚ ℂ`, not an abstract field assumed to contain the required coefficients.

The code proves that i is algebraic from the polynomial X²+1, proves closure of polynomial lifting under the operations actually used by the finite matching formulas, and lifts the factorial coefficients, inverse polynomials, matching polynomials and both exceptional-root polynomials into that algebraic subalgebra. A root of a nonzero lifted polynomial is algebraic over this subalgebra, and the checked transitivity theorem then proves it is algebraic over ℚ.

Consequently:

- For algebraic n outside 0,+1,−1, any hypothetical nonzero multiple zero of the actual TM determinant is algebraic over ℚ.
- For the same n, any hypothetical common nonzero determinant zero of two distinct natural degrees is algebraic over ℚ.
- Evaluating the actual rational matching quotient at algebraic nonzero n,z gives an algebraic value. Thus either hypothetical exceptional pole would yield a nonzero algebraic number `2*i*n*z` whose actual complex exponential is also algebraic.

All factorial-series, derivative, quotient and nonvanishing hypotheses in these consequences are discharged by the preceding checked modules. In particular, the root's algebraicity is a conclusion rather than a premise of the exceptional-root theorems. The final exponential obstruction is unconditional under the stated determinant-zero hypotheses; there is no assumed transcendence principle and no pole-simplicity premise.

The one remaining number-theoretic step is the full theorem that the exponential of a nonzero algebraic complex number is transcendental. The cached mathlib version contains `Lindemann/AnalyticalPart.lean`, including polynomial exponential approximations, but not this complete transcendence theorem. This file does not turn the obstruction into False or claim simplicity/separation. Pole existence and Fredholm/operator multiplicity also remain separate formal obligations.

Self-audit checked the coefficient lift, map/evaluation compatibility, nonzero-polynomial transfer, restriction of scalars, inverse-coordinate recovery of z, and the nonzero exponential argument. The scope matches the actual complex definitions from the manuscript. All 24 fully qualified theorem reports are standard-only (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`, `admit`, or new axiom. Evidence: `lean/logs/modal-algebraicity-check.log`.

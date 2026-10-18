# General Riccati-Hankel Wronskian checked from factorial series

Source: `lean/ModalWronskian.lean`; namespace `OQ14.ModalWronskian`.
This extends the frozen `ModalAlgebra.lean` without changing its definitions.

The actual factorial coefficients satisfy the adjacent-coefficient recurrence. Substitution into the finite Laurent sum proves the polynomial radial equation, including the last-index cancellation. Actual complex derivative theorems then prove the Riccati radial ODE for the outgoing and incoming exponential expressions, and the derivative of their Wronskian is zero at every nonzero complex argument.

The normalization does not assume a Wronskian identity or an asymptotic expansion. Cancelling the two exponential and phase factors expresses the Wronskian as a Laurent polynomial. Under `w=1/z`, this is the entire finite polynomial

`w^2 (Qminus Qplus' - Qplus Qminus') - 2 i Qplus Qminus`.

The code proves the inverse-coordinate identities from the same finite factorial sums and proves the actual derivative is zero away from zero by the radial ODE. At zero the derivative vanishes because the opposite-phase first coefficients cancel; both Q values at zero are exactly one. The standard zero-derivative constancy theorem for an everywhere complex-differentiable function now gives the exact normalization `-2*i`. In particular, this works for every natural degree, including zero, and every nonzero complex argument, with no real-frequency restriction.

Consequences checked in the same module:

- Outgoing/incoming matching coefficients cannot both vanish for any degree and nonzero n,z.
- The plus coefficient is nonzero at every actual TM determinant zero with nonzero n,z.
- Any hypothetical multiple zero of the actual TM determinant satisfies both the exact rational pole equation and the actual rational derivative condition, in every degree. The nonzero-coefficient conditions have been proved, not assumed.

Self-audit: derivative statements are `HasDerivAt`, not symbolic placeholders. The finite series are the frozen factorial definitions. All transitions involving inverse arguments assume their nonvanishing; the inverse-coordinate polynomial itself is defined and differentiated at zero without invoking a singular-chain rule there. The final matching lemma uses the Wronskian at both z and n*z, which are nonzero by the theorem hypotheses. No algebraicity, pole simplicity, operator multiplicity, or existence conclusion is silently imported.

The Lindemann-Weierstrass step, generic rational-function algebraicity/separation, resonance existence, Maxwell Fredholm theory, and the continuum device theorem remain outside this module. It supplies a real general-degree analytic identity required by the manuscript, not the entire modal theorem.

All 26 named theorems have fully qualified axiom reports outside the namespace. The checked reports use only the standard `propext`, `Classical.choice`, and `Quot.sound` foundations. There is no `sorry`, `admit`, or new axiom. Compiler evidence is saved in `lean/logs/modal-wronskian-check.log`.

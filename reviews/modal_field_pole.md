# ModalFieldPole — actual meromorphic shell-response pole

Source: `lean/ModalFieldPole.lean`

SHA256: `961D53192B2E5DF8B9DEDED31184441AE6699A20F15DFA80C2A96693CD31843C`

Evidence: `lean/logs/modal-field-pole-check.log`. All 14 exported theorems compile cleanly with only `propext`, `Classical.choice`, and `Quot.sound`.

The numerator is the actual outgoing row of the matching adjugate, multiplied through the bounded shell field map. Actual scalar differentiability on the complement of zero yields analytic determinant and numerator coefficients; the proved shell holomorphy yields operator-valued numerator analyticity.

The regularized operator is explicitly the numerator divided by the determinant's actual divided slope at the proposed pole. The determinant's proved power series gives the divided slope's analytic power series. At the center its value is the actual nonzero determinant derivative, so the regularized operator is analytic there. Its value is exactly the previously checked nonzero physical shell residue.

The exact punctured formula is response(k) = (k−k₀)⁻¹ regularized(k). Only k−k₀ is canceled; the formula is valid even at another determinant zero under Lean's total inverse convention. This proves standard `MeromorphicAt` with order exactly −1. The high-quality existence theorem uses the already proved actual fixed-degree simple determinant zeros.

Self-audit: checked finite-dimensional coefficient identities, operator-valued analytic composition, actual divided slope, nonzero derivative use, punctured normal form and standard order characterization. No genericity or abstract pole premise is used.

Independent audit: channels read the complete source and confirmed all steps and the exact two-data shell-response scope. No defect was found.

Scope: these are genuine simple poles of the spherical matching response with actual outgoing fields on a bounded shell. This does not identify the full Maxwell resolvent or establish cross-degree isolation. The next module connects these same residue amplitudes to the actual assembled global weak mode.

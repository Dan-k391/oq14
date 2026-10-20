# ModalFieldResidue — checked shell response residue

Source: `lean/ModalFieldResidue.lean`

SHA256: `91611FD3933507DD130FC070F6F57021A2E34F43DF3C4377D27AC67DBD4D74A0`

Evidence: `lean/logs/modal-field-residue-check.log`. All 13 exported theorems compiled with only `propext`, `Classical.choice`, and `Quot.sound`.

The response is a bounded complex-linear map from the two matching data to the actual electric/magnetic field pair in the volume L2 space of the shell 1 ≤ |x| ≤ 2. Its representative agrees almost everywhere with the actual outgoing fields with amplitude supplied by the proved matching inverse.

The finite-basis coefficient calculation upgrades the existing amplitude residue limits to operator norm. The continuous bilinear `smulRight` map, together with the actual shell-L2 continuity, gives the operator-norm field residue limit. The residue is nonzero: a nonzero matching residue vector has nonzero outgoing amplitude, and the actual unit outgoing shell field has nonzero L2 norm. Its range lies in the line spanned by this field. The final existence theorem uses proved fixed-degree high-quality simple determinant zeros.

Self-audit: checked both coefficient formulas, subtype punctured-neighborhood transport, operator-norm topology, actual representative identities, and the nonzero witness. No point-value witness on a null surface is used to establish an L2 norm. No genericity or pole-identification premise is introduced.

Independent audit: channels read the complete source and confirmed all arguments, including finite-basis operator-norm convergence, the nonzero outgoing amplitude, and the punctured-frequency pullback. No defect was found.

Scope: the checked result is an actual operator-norm residue asymptotic. Banach-valued holomorphy of the unscaled field family is a separate next bridge. This source does not identify the response with the full Maxwell resolvent, prove cross-degree pole isolation, or assert a modal normalization.

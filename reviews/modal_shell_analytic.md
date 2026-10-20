# ModalShellAnalytic — actual Banach-valued analytic field

Source: `lean/ModalShellAnalytic.lean`

SHA256: `A11A0AD02590353C9510E84406CFCDFBEA72AFE1132D85B28FD0CBF926FADDDD`

Evidence: `lean/logs/modal-shell-analytic-check.log`. All 17 exported theorems compiled with only `propext`, `Classical.choice`, and `Quot.sound`. Two harmless `ring_nf` tactic suggestions are retained in the raw output.

The proof constructs the radius, inverse radius and coordinate functions in the Banach algebra of continuous complex functions on the compact physical shell. The algebra exponential of `I*k*radius` is analytic in the uniform norm; evaluation through an actual continuous algebra homomorphism proves that it equals the ordinary complex exponential pointwise.

The explicit degree-one Riccati--Hankel formula and its derivative are then represented by finite products and scalar inverses in this algebra. The actual radial electric and magnetic coefficients are analytic for every nonzero complex frequency. Fixed continuous linear coordinate embeddings assemble the complete field pair, and an exact pointwise identity identifies it with the existing outgoing Maxwell fields. Applying the genuine continuous-map-to-L2 map proves analytic dependence in the actual shell volume L2 space.

Self-audit: checked inverse-radius continuity on the shell, the Hankel derivative sign, all five nonzero Cartesian field components, the magnetic factor `I*k^2/k`, the actual continuous-map and L2 identities, and the transfer of the nonzero L2 norm. This is not an inference from pointwise analyticity.

Independent audit: channels read the complete source and confirmed the algebra-homomorphism evaluation, Hankel derivative term, fixed coordinate embeddings, exact Maxwell field identities and uniform-norm-to-L2 analytic transfer. No defect was found.

Scope: this module proves holomorphy of the actual outgoing field family. The matching response's simple-pole normal form is the next module; full Maxwell resolvent isolation remains separate.

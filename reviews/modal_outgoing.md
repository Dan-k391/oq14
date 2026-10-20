# ModalOutgoing — exact complex-frequency radiation condition

Source: `lean/ModalOutgoing.lean`

SHA256: `CC874533ACE156E606273AF046711E6133AD0348CCF26D36829CFA2A791F6946`

Evidence: `lean/logs/modal-outgoing-check.log`. All 22 exported theorems compile with only `propext`, `Classical.choice`, and `Quot.sound`; raw output retains two harmless `ring_nf` suggestions.

The actual degree-one outgoing Hankel fields are evaluated on a ray with Euclidean unit direction d. After multiplication by r exp(−ikr), their exact radial coefficients are

- Electric axial coefficient: b(−ik + 1/r + i/(kr²)).
- Electric radial-angular coefficient: b(ik − 3/r − 3i/(kr²)).
- Magnetic swirl coefficient: b(−ik + 1/r).

The exact weighted defect H − d×E is −bi/(kr²) times (d_y, −d_x, 0). Its norm is bounded uniformly in direction by |b|/(|k|r²), using the project's component-sup vector norm and Euclidean unit direction. The proof gives the actual far-field limits, tangential relation, and a direction with nonzero electric and magnetic far field whenever b and k are nonzero.

The spatial normalization x/|x| is constructed explicitly. The same estimate proves the exponentially weighted outgoing condition along every path with radius tending to infinity, including varying angular directions.

Self-audit: checked the Hankel derivative sign, electric and magnetic coefficients, the cross-product convention, complex-frequency exponential cancellation, norm conventions, all inverse-radius limits and the exact conversion from rays to general exterior points.

Independent audit: channels read the complete source and confirmed the exact formulas, defect sign, direction-uniform bound and arbitrary escaping-path limit. No defect was found.

Scope: the exponential weight is essential at a resonant frequency in the lower half plane; no false unweighted decay condition is asserted. The next module instantiates this explicit condition for the already checked global weak residue mode.

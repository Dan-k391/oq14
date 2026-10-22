# Independent audit: RiccatiTransmission

Frozen source: lean/RiccatiTransmission.lean.
SHA256: 9673A92F9CC282FB03F476DBEC5AC0259F7715A9CD8E03389F8643A987471035.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all three reports standard-only.
Log: lean/logs/RiccatiTransmission-independent-continuation.log.

Actual position cross products of the explicit TE and TM fields agree on a
positive-radius sphere when the actual Riccati values and correct scalar
momenta agree. TE uses u'=v'; TM uses u'/epsilon=v'/zeta. Tangential E and H
matching is derived from the earlier actual Debye component formulas and
true derivatives at the interface, not supplied as a premise. The TM field
normalization is epsilon inverse times N and -I*k times M, consistently
producing the epsilon-weighted derivative state.

This is a pointwise interface matching theorem. Its hypotheses include actual
quotient smoothness, actual derivatives, positive radius and homogeneous
harmonic polynomial data. It does not itself prove Maxwell equations or
Sobolev gluing. Algebraic division uses Lean's totalized inverse, so nonzero
frequency/material assumptions needed for physical Maxwell specialization
remain in the corresponding separate positive-coefficient wave results.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `9673a92f9cc282fb03f476dbec5ac0259f7715a9cd8e03389f8643a987471035`. Independent log `lean/logs/RiccatiTransmission-independent-continuation.log`, SHA256 `faa1c8c720de0dc894fa94b7faa0b6986b1fcb1003d749a537dc5ce1d121e6a7`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

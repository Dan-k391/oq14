# ModalPoleRadiation — the same residue mode satisfies radiation

Source: `lean/ModalPoleRadiation.lean`

SHA256: `44E32CBD756CF9E8EB175B99A922446656AADB4290250B883390BB38C13CC86F`

All seven selected exports compiled with an importable object and only
`propext`, `Classical.choice`, and `Quot.sound`.

The actual pole residue amplitudes already used for the global weak mode
are used unchanged in the exterior Hankel formulas. The actual normal is
the radius vector divided by its Euclidean norm. The weighted radiation
defect agrees exactly with the outgoing exterior defect beyond the unit
sphere, and its norm is bounded by the outgoing residue amplitude divided
by the frequency norm and radius squared.

The limit holds along every path whose radius tends to infinity. Both
actual electric and magnetic ray limits use the same outgoing residue
amplitude. A nonzero actual shell residue forces that amplitude to be
nonzero, so both far fields are nonzero in a common unit direction.

The existence export joins the actual order-minus-one shell response pole,
the same nonzero residue input, the global weak Maxwell equations, the
weighted radiation limit, and the nonzero electric and magnetic far fields.

Self-review checked the shared input and frequency throughout, the exact
exterior identity, pathwise eventual exterior membership, correct complex
exponential weight, and nonzero amplitude argument. Root independently
read the complete source and passed its final audit after the seven reports
were appended.

Scope: the result concerns the constructed spherical matching shell
response and its actual global weak residue mode. It does not identify the
full Maxwell resolvent or establish cross-degree pole isolation.

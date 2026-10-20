# AngularPowerZero verification

Frozen source: `lean/AngularPowerZero.lean`.
SHA256: `12BD6CC443144BFB6B341DC5601B5C21EC93872176FCEE6221C3B1F8E1FD8CC9`.

The actual spherical far power is zero exactly when the electric far-field
amplitude vanishes at every sphere point, equivalently at every real unit
direction. This strengthens the existing almost-everywhere conclusion using
the proved full support of the actual angular measure and the established
continuity of the actual electric amplitude. The spherical measure support
instance is transferred explicitly to the existing angularMeasure alias.

The exact magnetic/electric amplitude tangential relation gives magnetic
vanishing from electric vanishing, with no further frequency restriction.
Both amplitudes therefore vanish pointwise when farPower is zero. Uniqueness
of the actual spherical-power limit then proves that zero limiting spherical
power is equivalent to pointwise electric-amplitude vanishing, and implies
both amplitudes vanish in every unit direction.

These statements concern the actual real-frequency compact-source Maxwell
fields and their proved amplitudes. Exterior-field vanishing from zero
far-field amplitudes is not asserted here.

Pinned Lean 4.19 compilation and object export completed with exit 0. All six selected theorem dependency reports contain only propext, Classical.choice, and Quot.sound. Root completed the independent full-source audit at the frozen hash above and accepted all six results. Final freeze PASS.

Root integration trimmed a surplus terminal blank line only. The clean aggregate provenance records the packaged source bytes; targeted hashes above remain the original verification evidence.

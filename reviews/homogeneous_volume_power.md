# HomogeneousVolumePower verification

Frozen source: `lean/HomogeneousVolumePower.lean`.
SHA256: `14FFA565AD8478049A36418E21E9FFC70EE8650394FC4C04B615F816881C007A`.

An actual homogeneous DynamicVolume.volumeBlock solution, with compactly
supported bounded measurable nonnegative susceptibility and arbitrary support
radius, generates the existing actual exterior electric representative and
the literal magnetic source response. There is no small-volume assumption.

The zero incident datum is handled as an L2 equivalence class: its actual
zero representative identity is proved almost everywhere after transporting
Lp.coeFn_zero through the measure-preserving coordinate map. This is then
used in the actual volume_solution_testMaxwell theorem with zero incident
fields and zero datum. The resulting weak Maxwell equations are transferred
to the exterior representative using its actual global AE equality. The
locally L2 electric and magnetic response properties use existing unconditional
response theorems, with no inverse or smallness premise.

The actual dielectric is measurably bounded by 1+c.bound, derived from the
coefficient data. Outside the source ball, the electric representative is
exactly the ordinary exterior electric source integral; magnetic equality is
by its actual definition. RadialFlux.maxwell_farPower_zero consequently gives
zero actual outgoing far power. AngularPowerZero then gives vanishing electric
and magnetic far-field amplitudes in every unit direction. The proved actual
spherical-power limit is zero as well.

This module proves zero outgoing power and zero amplitudes. It does not
assert the further Rellich conclusion of exterior-field vanishing or injectivity
of the actual volume block.

Pinned Lean 4.19 compilation and object export completed with exit 0 and no warnings. All 11 selected theorem dependency reports contain only propext, Classical.choice, and Quot.sound. Root completed the independent full-source audit at the frozen hash above and accepted the complete actual-field chain. Final freeze PASS.

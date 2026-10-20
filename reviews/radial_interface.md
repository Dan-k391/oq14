# RadialInterface scope and self-audit

`lean/RadialInterface.lean` supplies 23 checked analytic results for actual radial profiles joined at the unit sphere.

The first two results allow the origin in addition to the sphere as an exceptional set for classical derivatives. The origin is removed by discarding the measure-zero transverse line parameter, while the sphere is treated with the continuous off-countable fundamental theorem of calculus. No interface cancellation is assumed.

The radial profile has an inner branch on norm at most one and an outer branch beyond one. Inner continuity is needed only on nonnegative radii, outer continuity only on positive radii. Equality of their values at one proves continuity of the assembled scalar field. The actual off-origin and off-interface derivative is computed by local equality to one branch and the Frechet chain rule.

The derivative field is proved locally integrable. Its norm is bounded by the sum of two continuous profile norms: the inner derivative at the actual radius, and the outer derivative at the radius clipped below at one half. The coordinate ratio has norm at most one. The clipping appears only in the bound, not in the physical field.

Coordinate-weighted radial fields are differentiated by the actual product rule. Their derivatives are locally integrable using compact-set integrability and continuous multiplication. The weak gradient curl theorem applies these identities to actual C2 test derivatives; it therefore permits a normal jump without assuming that jump cancellation.

The final curl theorem states a real integration-by-parts identity for continuous vector fields whose genuine off-sphere and off-origin coordinate derivatives are locally integrable. Actual Maxwell mode profile instantiation is separate.

Self-audit checked the derivative signs, the origin/sphere null sets, branch boundary assignment, all norm-ratio bounds, measurability of actual Frechet derivatives, and the test smoothness requirements. No new axioms, no PDE solution assumptions, and no abstract replacement of the true differential operators are introduced.

Evidence: `lean/logs/radial-interface-check.log`, exit zero with 23 reports using only the standard Lean axioms.

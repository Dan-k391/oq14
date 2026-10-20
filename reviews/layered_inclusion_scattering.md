# Maxwell scattering for finite layered inclusion devices

Source: `lean/LayeredInclusionScattering.lean`.

SHA256: `1732380CA3E51C4A45FCAA36B84FA64538313ED989A1FB5FCB28ED07A0530214`.

Author final compiler exit 0; importable object 197856 bytes. All 11 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/layered-inclusion-scattering-check.log`.

Every result invokes the actual constructed layered-inclusion partition and its derived exterior seed. Inputs are finite literal inclusion centers/radii, strictly ordered positive radial cuts, positive inclusion radii, strict pair separation, strict containment in the innermost core, the actual bounded nonnegative susceptibility coefficient, its compact support, and actual AE positive dielectric values on the literal cells. No partition, connectivity, propagation, real-frequency uniqueness or operator invertibility is assumed.

The actual real volume block is a unit at every positive frequency. Its literal `MaterialField.solution` satisfies the volume equation and is the unique volume unknown. The physical incident datum yields actual `PiecewiseScattering.PhysicalFields`, including weak dielectric Maxwell, all-ball electric/magnetic L2, actual polarization, exterior continuity and an inverse-square Silver--Mueller defect bound. A wrapper accepts actual classical vacuum incident fields.

The actual complex-frequency volume block has no exceptional positive real point, and its inverse is analytic near every positive real frequency, both as an operator and applied to a fixed source. An actual positive-radius complex neighborhood is supplied. The existing unconditional `PiecewiseRealSpectrum.inverse_real_apply` identifies this complex inverse on the real axis with the same literal real solution.

Scope: actual finite spherical inclusions inside finitely many concentric material layers. The result does not assert arbitrary outgoing PDE-to-volume equivalence, a full Maxwell resolvent pole, cross-degree pole isolation, or a completed channel construction.

Independent reviewer continuation_review_sol read the complete source and
its actual constructed geometry, together with the reused actual Maxwell
uniqueness, PhysicalFields, volume inverse, and complex analytic inverse
interfaces. Independent pinned Lean 4.19 compilation completed with exit 0
at the exact hash above. All eleven dependency reports list only the three
standard foundations. The hash remained unchanged after compilation.

The proofs discharge the partition and exterior-seed obligations by actual
geometry. Actual homogeneous Maxwell continuation and exterior Rellich then
give volume-kernel triviality, and the proved compact alternative gives the
actual volume unit. The literal solution therefore satisfies its actual
volume equation. Maxwell fields, polarization, and radiation properties
follow from that equation; they are not hypotheses. Positive-axis complex
regularity is derived from actual real invertibility and analytic inversion.

No mathematical scope issue was found. The finite compactly supported
susceptibility class is nonnegative, so the actual dielectric is at least
one; the explicit positive cell values identify that same coefficient.
Repeated values are allowed. No uniform response bound over growing radial
stacks, small-inclusion asymptotic expansion, all-order Green limit,
power-normalized scattering-map construction, or full channel theorem
follows from this module alone. No frozen proof source was edited.
Independent mathematical and compiler audit: PASS.

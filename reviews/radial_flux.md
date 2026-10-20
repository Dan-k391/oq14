# Actual weak conservation to zero outgoing power

PolarIntegration has five exports, RadialFlux has nine. Both passed pinned
compilation and importable-object generation. Reciprocity Sol independently
read their complete sources and recompiled both without warnings; all
dependency reports contain only propext, Classical.choice and Quot.sound.

Targeted source SHA256:

- PolarIntegration: `4b7f553071f8fb4a1b0dc882f19966f346765907bb67fe3994eb2a60e8fd5c84`
- RadialFlux: `ac4995bd6d1792e25b55cf57ee729975ae277a0e8551328dacd88e2284590ab3`

The polar formula uses the actual Euclidean polar homeomorphism and the
angular measure obtained from volume. Removing the origin is justified by
its zero volume. The radial density is exactly the three-dimensional
Jacobian r squared. Product integrability and Fubini are proved from the
actual integrable spatial pairing.

RadialPowerTest constructs compact C1 radial tests with genuine Frechet
derivatives. RadialWeight proves that the resulting nonnegative scaled
density has a fixed strictly positive integral and vanishes below its
scale. RadialFlux combines these with MaterialPower's weak Maxwell theorem
to obtain an integrable weighted spherical flux with integral zero.

The final limit argument does not assume flux vanishing. A positive
nonnegative far limit would make the spherical flux exceed half that
limit beyond some radius. Choosing the test scale beyond that radius
gives a strictly positive weighted integral, contradicting the proved
identity. The actual compact-source spherical limit supplies the limit
and its nonnegativity. Exterior representative equality is explicit,
and local L2 regularity and the weak Maxwell equations are required.

This closes the weak-power-to-zero-far-power bridge. It does not prove
the exterior Rellich theorem or continuation through the material.
HomogeneousVolumePower separately derives all field hypotheses from an
actual homogeneous volume solution, without a small-support condition.

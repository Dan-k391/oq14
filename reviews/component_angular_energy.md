# ComponentAngularEnergy — actual component mass from vector spherical energy

Source: `lean/ComponentAngularEnergy.lean`

SHA256: `B03BEA48672524E6DE56689A34D9CA369E7E569E5B1F46861D764685B5BEAE05`

Evidence: `lean/logs/component-angular-energy-check.log`. Final compile
exited zero without warnings, created an importable object (204624 bytes),
and emitted nine selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The actual vector energy is the sum of the three squared component norms.
Each component squared norm is therefore at most the vector energy.
Multiplying by the nonnegative radius-squared factor and integrating over
exactly AngularPower.Sphere/angularMeasure gives the scalar sphericalMass
bound by AngularEnergy.sphericalEnergy. Sphere continuity supplies actual
integrability of both sides under the finite angular measure.

Scalar mass is nonnegative for every field and radius, so eventual sphere
continuity and vector spherical energy tending to zero imply component
mass tending to zero by a direct squeeze. There is no radiation,
smoothness, or PDE premise in this generic implication.

The actual electric and magnetic specializations use the existing actual
compact-L1-source sphere continuity theorem and the proved vector energy
decay from farPower=0. Consequently each of the six actual Maxwell
components has exactly the sphericalMass decay required by scalar
Rellich. The theorem is valid for every real frequency; scalar Rellich
will separately require its positive-frequency premise.

Self-review checked the exact vector energy definition, all three
component inequalities, radius-squared factor, integral monotonicity and
integrability, nonnegativity squeeze, and actual E/H representatives.
No scalar or vector Rellich conclusion is assumed or asserted here.

Root independently read the complete final source at the recorded hash
and passed all nine exports. Source frozen.

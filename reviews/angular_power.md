# Actual spherical outgoing power

AngularPower has 17 exports. Root compilation and importable object generation
passed; all reports use only propext, Classical.choice and Quot.sound.

Targeted source SHA256:
`23a23d2572d4d5640cc710ebb69c2c23f49b5f6b61292efef1f90d721ee89630`.

The spherical measure is the actual polar measure derived from Euclidean
volume. Scalar far amplitudes are continuous by a source-integrable majorant.
Electric amplitude continuity follows from the actual transverse formula.
The actual scaled potential has a direction-independent bound. Finite sums,
the electric and magnetic inverse-square error bounds, and the exact complex
scaling of power give a common bound for all unit directions and all
sufficiently large radii.

Actual exterior continuity supplies angular measurability. Dominated
convergence with the finite spherical measure proves that the actual
spherical power tends to half the integrated squared electric amplitude.
The limit is nonnegative, and zero is equivalent to almost-everywhere
vanishing of that amplitude. No zero-power condition or outgoing uniqueness
conclusion is assumed in this limit theorem.

Reciprocity Sol independently read the complete source and recompiled the
exact file: exit zero, seventeen standard-only dependency reports. The
independent log is `lean/AngularPower.independent-sol.log`.

Pointwise zero follows in the separate AngularPowerZero module using the
proved open-patch positivity of SphereMeasure. The weak Maxwell conservation
law still needs to be connected to zero total outgoing power, and a Rellich
and material unique-continuation argument is still required for uniqueness.

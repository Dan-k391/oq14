# Actual local magnetic H1 regularity

`lean/WeakPoynting/LocalRegularity.lean` is frozen at SHA-256 `9f2e673dd274fb9acd7d56fe4068aa10de8e211c88fd7ffed9cbf444a0468861`. Direct Lean 4.19.0 compilation exited zero with nine selected axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Complete output and source hashes are in `local-regularity-verification.txt` and `local-regularity-provenance.json`.

The final theorem `OQ14.LocalRegularity.maxwell_magnetic_local_h1` starts from actual regional H(curl) fields satisfying the almost-everywhere source-free Maxwell curl equations, with constant permeability one and nonzero real frequency. For every compact set K contained in the open region Ω, it constructs an open U with K contained in U contained in Ω, a genuine global L2 vector field F, and nine genuine global weak L2 derivatives of F. On U, F agrees almost everywhere with the original magnetic field H. This is an explicit local H1 statement, without assuming globally finite energy of the physical fields.

The first Maxwell equation and the already proved weak divergence-of-curl identity yield magnetic divergence zero. The existing divergence-of-curl theorem uses compact C2 tests. The proof respects that class: it introduces the corresponding actual test predicate, uses smooth convolution kernels, and uses C2 interior cutoffs. There is no assumed upgrade from C2 to C1 tests. The resulting weak derivatives themselves satisfy the ordinary compact C1 test identities.

The cutoff divergence formula is derived from the literal product test χφ and the proved derivative product pairing. Both the field and its divergence are actual restricted-measure L2 multipliers extended by zero. Their support and weak equations are proved, without imposing a boundary condition on the original field. `maxwell_cutoff_magnetic_regularity` retains the exact total derivative-energy identity for each such cutoff.

Finally a smooth cutoff equal to one near K is constructed using the existing smooth Urysohn theorem. The open set U is the interior of its one-level set intersected with Ω; agreement of the actual L2 extension with H is proved on that set.

Permittivity is allowed to be an arbitrary real function satisfying the actual curl equations; no derivative or continuity of permittivity is used. The conclusion does not provide a boundary trace, compact embedding theorem, existence of scattering solutions, or the full original OQ14 claim.

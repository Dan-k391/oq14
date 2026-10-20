# Independent actual radial-source Green audit

Source: `lean/RadialSource.lean`.
SHA256: `A5661ED3236EC01A1AE07B4762368EE9725FD95DF08B2799237DC83274B6ACF4`.

Independent reviewer continuation_review_sol read the entire frozen source
and the actual Hankel basis, layer, propagation and stack dependencies.
Independent pinned Lean 4.19 compilation exited 0 without warnings. All 16
reports use only `propext`, `Classical.choice`, and `Quot.sound`. Log:
`lean/logs/RadialSource-independent-continuation.log`. Hash unchanged after
compilation; forbidden source scan clean; no source edits.

Coefficients are the inverse actual vacuum fundamental matrix applied to
the actual stack continuation of the outgoing Hankel state. Conserved
imaginary load one forces the second coefficient beta nonzero, and the
defined gamma=alpha/beta has imaginary part -1/abs(beta)^2. Gamma norm bounds
come from genuine coefficient energy, actual stack propagation and actual
low-angular-range vacuum state bounds.

The defined core wave chi+gamma*psi satisfies the actual homogeneous radial
ODE, has Wronskian one with psi, and matches the continued state divided by
the proved nonzero beta at the core boundary. The scalarGreen min/max formula
is the genuine regular/core-wave product. scalarGreen_jump computes the
difference of its two smooth branch derivatives and proves it equals one.
It is not a separate assertion of a global distributional source identity.

The low-range physical chain estimate invokes actual shared radii through
Chain. Other algebraic continuation statements remain meaningful for arbitrary
finite lists of actual layer transfers and do not assert adjacency absent
Chain. No global spatial Maxwell field, dyadic completeness identity,
finite-stack parity-kernel identification or all-order Green convergence is
claimed. No scope issue found. Mathematical and compiler audit: PASS.

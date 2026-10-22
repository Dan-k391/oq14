# Derived norm bound for actual finite-sphere interaction residuals

Source: `lean/FiniteSphereResidualBound.lean`.
SHA256: `850A7982C950BC301A57A8D33B44AB9E50DFC56C11DA1B5EBA710806C9A13D62`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all three reports use only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/FiniteSphereResidualBound-final.log`. Root independent complete-source mathematical review and pinned compiler also pass: exit 0, no warnings, standard-only reports. See the corresponding lean/logs/FiniteSphereResidualBound-root-audit.log audit log.

Actual center separation delta and radii at most delta/4 imply geometric
disjointness. The previously proved exact cross-field residual and actual
Newton cross-field estimates then give a uniform bound inside the actual ball
union. Outside that union the actual residual is zero.

A genuine L2 indicator of the actual finite support majorizes each actual
residual component. Its norm is the square root of the actual union volume.
The resulting genuine vector L2 residual norm is bounded by
3 sqrt(chi) interactionBound sqrt(volume(union)), with interactionBound the
explicit finite sum of (4/3) radius_j^3/(delta/2)^3 times the physical constant
polarization component norms. No interaction norm or convergence conclusion
is supplied as a premise.

This is an actual residual bound for the finite isolated-sphere trial sum.
The comparison with the literal parity-kernel inverse and the small-radius
family estimates are subsequent steps; this is not an arbitrary-source
cross-interaction operator norm theorem or a finite-stack Green identification.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 3 reports using only standard foundations. Final source SHA256 `850a7982c950bc301a57a8d33b44ab9e50dfc56c11da1b5eba710806c9a13d62`. Independent log: `lean/logs/FiniteSphereResidualBound-root-audit.log`; log SHA256 `8f1a504c02960b5d3178f3c3ea4f7dafe3197067b9fef4fdd7f656368eee8420`. This certifies the stated scope, not either complete OQ14 construction.

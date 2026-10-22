# Genuine L2 gradient and Hessian of the uniform ball potential

Source: `lean/StaticBallL2.lean`.
SHA256: `7B7046D2C6993A864DF0636FC5C389675DDBB58C9EC8976BFDEABB45BBC2D1AE`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All eleven selected reports use only propext,
Classical.choice, and Quot.sound. Log: `lean/logs/StaticBallL2-final.log`.
Root independent full-source mathematical review and pinned compiler also
PASS at the same exact hash, with no warnings and all eleven standard-only
reports (session 83577).

The proof integrates an actual three-dimensional radial majorant, splitting
the radial integral at the positive radius R. The majorant behaves as r^-2;
its square is integrable in dimension three. The explicit gradient is bounded
by (R^3/3) times this majorant and the explicit Hessian by (4 R^2/3) times it.
The Hessian's measurability uses actual continuous coordinate projections
on the Euclidean PiLp space. These give genuine MemLp witnesses, actual L2
elements, and AE identities with the previously constructed formulas.

This establishes L2 membership, not yet the Fourier weak derivative relation
or identification with the Newton/projection operator. Those remain necessary
before claiming the exact constant-ball response -P/3.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 11 reports using only standard foundations. Final source SHA256 `7b7046d2c6993a864df0636fc5c389675ddbb58c9ec8976bfdeabb45bbc2d1ae`. Independent log: `lean/logs/StaticBallL2-root-audit.log`; log SHA256 `201b3d0e7fc3b231510726747726958571471f25272a29f3f508dfd5ca31f3db`. This certifies the stated scope, not either complete OQ14 construction.

# Actual poloidal plane-wave coefficient

`lean/PoloidalPlaneWaveMoment.lean` has nine selected reports. Author final
compile and object completed with exit 0, no warnings, and only `propext`,
`Classical.choice`, and `Quot.sound`. Independent audit is pending.

The proof differentiates the literal toroidal sphere integral using the
previously proved dominated derivative interchange. The polynomial identity
`n cross (grad(P) cross n) = grad(P) - l*n*P` is derived from polynomial
Euler homogeneity and the unit sphere equation. Taking the actual Euclidean
curl then identifies the poloidal moment with
`(4*pi*I^l*k^l/(I*k))*tmElectric(solidWave)` for every nonzero real k and
every spatial point, including the origin. A division-free identity also
holds at k=0. Harmonicity is used through the verified toroidal moment.

The physical angular poloidal field is identified through its actual
polynomial restriction, not through an assumed transform convention.
Full dyadic Green assembly remains separate.

Source SHA256:
`cbd2571039fd0bf5e3f67b3c0129486e111c5de9b31596cc13e74101a982c831`.
Final log `lean/logs/PoloidalPlaneWaveMoment-final.log` SHA256:
`99c1a423cec46aa83c96ee5e21e593de3352fd01942dbc556903d41a6565609c`.

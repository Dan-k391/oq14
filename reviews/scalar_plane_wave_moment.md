# Actual scalar plane-wave harmonic coefficients

Author final PASS, October 23, 2026. Seven selected reports; no warnings or
errors; only standard Lean foundations. Source `lean/ScalarPlaneWaveMoment.lean`,
SHA256 `5710f9bfd5e569a4e1e831a54cdf5ec26a17f932ce3ec611b340bcb90fabc372`.
Final log `lean/logs/ScalarPlaneWaveMoment-final.log`, exit 0,
SHA256 `65efa3af1df44dc96780f324e1e1a8b8758336d7b37ca40abacaff2aae2fd3a5`.

The actual Green far-field moment and its actual source-normalized radial
coefficient identify the scalar plane-wave integral. The outgoing Hankel
factor is cancelled using its proved nonvanishing at a positive real radius.
Continuity extends the identity to the origin; spatial homogeneity extends
it to every real frequency. The positive-phase coefficient is exactly
4*pi*I^l*k^l times the smooth solid wave; the negative phase uses (-I)^l.
No plane-wave expansion or angular integral identity is assumed.

Unregistered pending independent audit and a later clean aggregate.

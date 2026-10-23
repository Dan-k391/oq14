# Actual toroidal plane-wave coefficient

`lean/ToroidalPlaneWaveMoment.lean` has six selected reports. The author final
compile and object completed with exit 0 and only `propext`,
`Classical.choice`, and `Quot.sound`. Independent audit is pending.

The proof establishes that every Cartesian component of the literal angular
toroidal field is a homogeneous harmonic polynomial of the same degree. The
actual scalar moment theorem therefore gives its exact sphere plane-wave
integral as `4*pi*I^l*k^l` times the globally smooth solid toroidal Debye
field. The equality holds for every real frequency and every spatial point,
including the origin. The equality with the solid field follows from the
actual differentiated radial scalar field and continuity at the origin.

This is an integral identity, not an assumed harmonic expansion or an
identification of the complete dyadic Green tensor.

Source SHA256:
`cc1ae926b442d1bbf54f92158c5485b204541118fdc968444a681eafdac78c1c`.
Final log `lean/logs/ToroidalPlaneWaveMoment-final.log` SHA256:
`6df00abb8faea83a534cc7b7e73ee7b197007a44b2db7515d33175c09ccb7287`.

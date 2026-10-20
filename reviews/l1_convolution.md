# L1Convolution verification

Frozen source: `lean/L1Convolution.lean`.
SHA256: `A13C3D9A21408EA59BB05B199A01EC51CBAF169B13B9C6D6E04ABA9B5FBAC987`.

Clean pinned Lean 4.19 compilation completed October 20, 2026. All 16 exported
theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no admissions or extra axioms.

For an actual complex L1 kernel, its ordinary Fourier integral is bounded by
the integral of its absolute value. This constructs a bounded scalar L2
operator with that exact norm bound. For every actual L1 intersection L2
source, bilinear Parseval and the proved ordinary L1 convolution Fourier
identity give equality of genuine test integrals. Compact smooth test
separation then identifies the L2 representative almost everywhere with the
literal spatial convolution. Consequently that convolution belongs to L2 and
satisfies Young's L1-L2 bound.

The boundedness of spatial convolution is a conclusion of this proof, not an
input. The explicit spatial identity currently requires the source to be L1
and L2, which includes the compactly supported material sources already
constructed in StaticNewton. The operator exists on all scalar L2.

The hotspots agent independently read the full source and accepted its
ordinary Fourier bound, spatial identification, and norm estimate on
October 20. No circular mapping assumption was found.

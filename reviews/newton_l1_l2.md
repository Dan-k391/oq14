# NewtonL1L2 verification

Frozen source: `lean/NewtonL1L2.lean`.
SHA256: `0C44B76BE988E07FE4E816AA074DE7414CC69593B3D71D4DED627952F7C5D51A`.

The pinned Lean 4.19 compiler completed cleanly on October 20, 2026. All 11
exported theorem reports contain exactly the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. No admissions or additional axioms occur.

Actual ordinary Fourier integrals of L1 intersection L2 functions agree almost
everywhere with the constructed Plancherel transform. This follows from actual
Fourier integral interchange, bilinear Parseval and separation by compact smooth
tests; no compatibility assertion is a premise.

The full spatial Newton-Hessian weak response for every actual integrable
square-integrable vector source is identified with `newtonOperator = -P`.
The theorem explicitly displays the source components and the spatial integral
against second derivatives of the test. A compact-support lemma supplies
integrability for square-integrable sources. The trace identity is exactly the
negative source distribution, retaining its contact term.

Root and hotspots independently read the full source and accepted it on
October 20. The peer audit checked the ordinary Fourier compatibility,
coordinate transport, integrability, literal spatial response and trace term.
No hidden spatial Fubini or Fourier identification premise was found.

This does not assert ordinary pointwise integrability of the singular Hessian
kernel. It identifies its full distributional convolution, including the source
term, with its uniquely bounded L2 realization.

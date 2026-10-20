# Actual harmonic moments separate continuous complex sphere functions

Source: `lean/HarmonicMomentSeparation.lean`.

SHA256: `77761814AA36D30ED41D856494211201978E3E323F8D225A3F400065BE2AE525`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All three exported theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final complete-source audit passed at this exact hash. The source is frozen.

The literal angular integral against a fixed continuous complex function defines a continuous real-linear functional on the normed space of continuous real sphere tests. Its construction uses actual complexification, pointwise multiplication, the continuous inclusion into L1, and Bochner integration. Zero bilateral moments against every actual homogeneous harmonic polynomial therefore annihilate the actual harmonic span. The proved Fischer harmonic-span density and closedness of the functional's kernel extend vanishing to every continuous real test.

Applying this conclusion to the real and imaginary parts of the original function gives zero integrals of their nonnegative squares. The genuine full support of the Euclidean angular measure, already proved in `SphereMeasure.lean`, upgrades the resulting zero-square identities to every sphere point. Both components vanish, so the original continuous complex function vanishes pointwise.

The only assumptions are continuity and the literal zero homogeneous harmonic polynomial moments. Harmonic completeness, pointwise separation, and the function's zero conclusion are proved, never assumed.

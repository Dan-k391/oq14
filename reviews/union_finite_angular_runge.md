# Author review: finite-angular Runge approximation on a union

Source: `lean/UnionFiniteAngularRunge.lean`, SHA-256 `722274446F3789F3C3359E749BFD280B91E030DC04546ACD5CCA1BA241ED7CC3`.
Final log SHA-256: `0FACE98CA4B0AA2361B36F82903C5FE518F3D9F4EF7877F4531CA1F338FD4D5F`. Object build exit 0; all six printed theorems depend only on propext, Classical.choice, and Quot.sound.

The approximation theorem takes a finite family of strictly separated closed balls, a positive wave number, and an actual compact L2 driving source that vanishes on their union. It returns one finitely supported transverse vector spherical-harmonic coefficient input whose actual Herglotz incident electric field approximates the source response in L2 on the entire union. The proof combines the previous finite-plane union Runge theorem with the proved uniform finite-angular approximation, then converts uniform error to union L2 error. It does not assume that the driving source is outside the enclosing ball. It does not establish a common material assembly, normalization, or hotspot conclusion.

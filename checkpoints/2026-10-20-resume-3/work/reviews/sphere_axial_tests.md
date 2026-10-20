# SphereAxialTests — author verification

Source SHA256: `94382D92104E50D593804BA31B46EB3AE95739D82DCACA12D95B9FBAEBD0D2CD`.
Pinned Lean 4.19 compilation and object emission exit 0, no warnings, all 15 dependency reports standard-only. Object 584024 bytes. Final log SHA256 `4225608A0303D25116AD15182D4892A4DD62F413AE73CC1BCC3A3E410A4079F3`.

The literal ambient latitude map has the actual vector derivative; its norm is exactly 1/sqrt(1-z²). Multiplication by (1-z²) gives the genuine tangent direction e₂-z n. Every ambient C1 real test therefore has its actual latitude derivative bounded uniformly in azimuth by C/sqrt(1-z²), using compactness of the actual unit ball and continuity of its Fréchet derivative. The pole majorant is integrable by the actual arcsine derivative and FTC. The final theorem applies the proved endpoint cap identity to every such genuine ambient test at each azimuth.

Scope: actual test calculus and per-azimuth cap identity. Actual sphere coarea/Fubini closure and weak tangential-gradient characterization are separate following sources. Parent independent complete-source/compiler audit requested.

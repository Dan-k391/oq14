# SphereMeasure verification

Frozen source: `lean/SphereMeasure.lean`.
SHA256: `94305C7AC8219271165FB3DE20291B775BA9C1BE6C95D550B12121ACD1B6A9A2`.

Pinned Lean 4.19 compilation and object export completed with exit 0. All
three selected theorem dependency reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The spherical measure is the actual `volume.toSphere` from the generalized
polar-coordinate construction. Every nonempty open sphere patch, multiplied
by an open radial interval inside the unit ball, lifts through
`homeomorphUnitSphereProd` to an open nonempty subset of punctured Euclidean
space. The punctured-space subtype inclusion is an open map into Euclidean
space, so this cone has positive Lebesgue measure by established Haar
positivity. The actual `toSphere_apply` formula, with dimension three,
therefore proves positive measure for the original patch. No measure-support
premise is supplied.

The resulting `IsOpenPosMeasure` instance targets `volume.toSphere` directly.
A continuous real function equal to zero almost everywhere for this measure
is identically zero. Combining this with the established nonnegative
integral-zero characterization gives the corresponding conclusion for a
nonnegative continuous integrable function of zero spherical integral.

Root completed the independent full-source audit at the frozen hash above and accepted all three selected results. Final freeze PASS.

Root integration removed surplus blank lines at end of file only. The clean aggregate build records the packaged source hash; targeted hashes above remain the original run evidence.

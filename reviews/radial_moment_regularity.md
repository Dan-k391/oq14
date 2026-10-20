# RadialMomentRegularity verification

Source: `lean/RadialMomentRegularity.lean`.
SHA256: `A5575D1FA08AFB8A76F29EECCD5650E4973EB23433757D97C43C847441B947F9`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All four selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Actual smoothness of u on the open exterior yields continuous actual first
and second Frechet derivatives there. The joint radius-direction map from
Ioi R times the sphere remains in this exterior for nonnegative R. Twice
applying these continuous linear maps to the actual sphere direction gives
a continuous integrand for momentDD. The actual finite angular measure,
compact sphere, and continuous parametric integral theorem yield
momentDD continuity on Ioi R. The already proved actual derivative
identifications give C1 momentD and C2 moment by the open-set derivative
characterization. No radial ODE or moment regularity is presumed.

Independent full-source review requested from root at this hash.

Root completed the independent full-source audit at this hash. Final freeze PASS.

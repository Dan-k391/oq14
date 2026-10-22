# Independent audit: SphericalMaxwellWaves

Frozen source: lean/SphericalMaxwellWaves.lean.
SHA256: 450C9209008535E6842FE0861393F5AF116FBADC58049D7BFE4B8602D0486C7C.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all eight reports standard-only.
Log: lean/logs/SphericalMaxwellWaves-independent-continuation.log.

Actual globally smooth solid-series waves yield TE and TM Maxwell fields
at every point, including the origin. Actual outgoing xi radial waves yield
the two Maxwell curl equations away from the origin. Both complex-parameter
and real-parameter formulations are proved. Genuine scalar Helmholtz equations
and all smoothness inputs to DebyeMaxwell are discharged using actual earlier
wave theorems, rather than assumed here.

Homogeneous harmonic polynomial data and q^2=k^2 epsilon remain explicit.
TE requires nonzero k; outgoing waves also require nonzero q and x. The
regular solid series handles q=0 algebraically when dispersion allows it.
The degree-zero toroidal field may vanish; nontriviality, completeness,
transmission interface matching, radiation conditions and spatial Green
reconstruction are not asserted by these wrappers. The underlying solid
wave normalization differs from the raw quotient by q^(l+1), as its actual
wave_regular_factor theorem explicitly records.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `450c9209008535e6842fe0861393f5af116fbadc58049d7bfe4b8602d0486c7c`. Independent log `lean/logs/SphericalMaxwellWaves-independent-continuation.log`, SHA256 `efbf2d028d223ea57ab126ff8f5eda454658a9e0f23f1d883919c0baba30989c`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

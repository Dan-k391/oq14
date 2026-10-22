# Exact isolated sphere response in material-weighted space

Source: `lean/StaticSphereMaterial.lean`.
SHA256: `34D6D749507D0AC2E2C0D92109E0591A72B3078F9F97A32112314857E7E2F001`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all eight reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereMaterial-final.log`. Root independent full-source
mathematical and fresh pinned compiler review PASS at this exact hash,
no warnings and all eight reports standard-only. Independent log:
`lean/logs/StaticSphereMaterial-root-audit-final.log`.

The actual susceptibility is chi on an arbitrary actual ball and zero outside,
for any nonnegative real chi. A genuine material-weighted trial is the constant
ball source with value 3 sqrt(chi)/(chi+3) E. Actual multiplication by sqrt(chi)
is proved to produce the physical polarization source 3 chi/(chi+3) E,
including chi=0.

The actual previously constructed Newton response then gives the existing
material-weighted static block applied to the trial equal to the actual
weighted forcing. The existing coercive block's actual Ring.inverse applied
to that forcing is proved equal to this trial. No static inverse action or
depolarization identity is supplied as a premise.

Scope: one ball, a constant incident vector, any center and positive radius,
and nonnegative susceptibility. Source errors for the dynamic/parity block,
variable incident fields, multiple inclusions, and finite-stack Green
identification are separate subsequent estimates.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `34d6d749507d0ac2e2c0d92109e0591a72b3078f9f97a32112314857e7e2f001`. Independent log: `lean/logs/StaticSphereMaterial-root-audit-final.log`; log SHA256 `d3e06a68ed78e0e412677149e6e75452a518b4d0eb0f04da9b5b9ad907502436`. This certifies the stated scope, not either complete OQ14 construction.

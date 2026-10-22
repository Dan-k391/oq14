# Actual inverse static plane fields versus exact finite dipoles

Frozen source: lean/StaticPlaneDipoleError.lean.
SHA256: D41754119379CA8CA9E26BE247975D0EF306777FFE87ED9FF15534FD1C96708B.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports standard-only. Log: lean/logs/StaticPlaneDipoleError-final.log.
Independent review is pending.

Literal field integrals respect actual source AE equality. The genuine finite
L2 polarization trial therefore has the exact finite center dipole profile at
every plane point, by the proved continuous single-ball identity and genuine
finite integral linearity. The actual material source has a continuous ordinary
Newton representative on its actual source-free strip, with AE identification
of the genuine existing StaticNewton.response on that 3D open strip.

The final family theorem constructs actual support data and a positive
small-radius range for moving finite centers. It gives the genuine continuous
Newton representative, its actual operator identification, whole-plane L1
integrability of its difference from the exact finite dipole profile, and an
explicit fixed-constant times a squared bound for that L1 error.

Its premises are actual uniform finite-center separation, enclosing geometry,
absolute center heights at least (gamma+rho)*a, actual incident derivative
bounds M/a and center amplitude bounds A/a, and actual weighted forcing
representatives. All inverse-source, moment, spatial operator, and plane-error
conclusions are discharged by proved theorems. None is a premise of the final
family result. No arbitrary 3D AE representative is restricted to the plane.

This is the static Newton part of the actual literal parity-kernel material
inverse. The dynamic spatial field, actual magnetic reaction field, full
whole-plane flux, and identification with a physical finite-stack Green
kernel remain separate remaining constructions.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `d41754119379ca8ca9e26be247975d0ef306777ffe87ed9ff15534fd1c96708b`. Independent log `lean/logs/StaticPlaneDipoleError-root-audit.log`, SHA256 `52e72d2e61533f3dda588ea41f9ad75e1242eb57f27d6b06a01d782811ad7c9a`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

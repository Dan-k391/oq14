# Actual static whole-plane source-error estimates with a moving gap

Frozen source: lean/StaticPlaneError.lean.
SHA256: F67AA30379D9CA2D0488D7064E91C2A888B805D30C63FE899EF7A246266BEB21.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports standard-only. Log: lean/logs/StaticPlaneError-final.log.
Independent review is pending.

For two actual integrable scalar sources separated from the observation plane
by positive d AE, genuine product integrability proves AE linearity of the
literal Hessian convolution over the plane. The actual difference field is
integrable and has L1 mass at most (3/d) times the actual source L1 difference.
With d=gamma*a and actual source L1 error at most C*a cubed, the actual plane
field L1 error is at most (3*C/gamma)*a squared. The latter requires positive
gamma and a, with no fixed-gap uniformity silently assumed.

No response or plane error convergence is a premise. The source error in
the generic scaling lemma is an explicit finite numeric input, discharged
by the subsequent actual finite-inclusion family theorem. All fields are
literal spatial integrals; no 3D AE restriction to a plane is used.
Identification of a continuous representative of the actual L2 Newton
operator near this plane remains separate, as does finite-stack Green work.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `f67aa30379d9ca2d0488d7064e91c2a888b805d30c63fe899ef7a246266beb21`. Independent log `lean/logs/StaticPlaneError-root-audit.log`, SHA256 `2ed0cceaa9223dd977a3edf465eac24b039153a042604cb06bfc9ed8c111cef9`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.

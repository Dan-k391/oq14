# Actual radial continuity and point-source derivative jump

Source: `lean/RadialSourceJump.lean`.
SHA256: `5A110C9B5FE7119A593B7B369F418CA9BC4A233622FB89FDE12FB597F26233C0`.

Author target plus importable object compiler exit 0, no warnings. Object 272472 bytes. Five selected reports standard-only. Log: `lean/logs/RadialSourceJump-final.log`. Forbidden-token scan passed.

The radial weak coefficients A=r^(l+2)U, B=(2l+2)r^(l+1)U and C=k^2 r^(l+2)U have actual smoothness and actual derivatives inherited from actual smooth side profiles. The already proved exact residual identity converts the actual homogeneous scalar radial ODE on each side into B'-A''=C. The literal weak radial source integral can consequently be replaced AE by its actual left/right profiles; the source radius is a genuine null singleton and tests vanish, with their derivatives, at every nonpositive radius. No continuity value at the singular radius is assumed.

The actual compact-test jump theorem then forces the one-sided smooth extensions to agree at s and gives the exact weighted derivative jump

    U_plus(s)=U_minus(s),
    s^(l+2) (U_plus'(s)-U_minus'(s)) = -S.

The proof explicitly cancels the nonzero positive-radius power in A continuity and uses it to cancel the B-A' terms. Its premises are actual side ODEs, actual side profile agreement away from the source and the actual weak point-source integral, not matching or derivative-jump conclusions. These are discharged for the literal Green kernel in ScalarGreenJump.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `5a110c9b5fe7119a593b7b369f418ca9bc4a233622fb89fde12fb597f26233c0`. Independent log `lean/logs/RadialSourceJump-root-audit.log`, SHA256 `05fc929af5b909b5bc099eb0136877f7118178d39a3144046d8470e524461ae1`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.

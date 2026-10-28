# ModalDipoleInfinity — author verification

Author PASS, 2026-10-27. Frozen source `lean/ModalDipoleInfinity.lean` SHA256 `2EFB72AAC5AB2F75FFF0632E5F0690907D4ACE154358291A3299AA681FD01F14`. Pinned Lean 4.19.0 final/object run exited 0, with no errors or warnings. All 20 selected declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

Final log: `lean/logs/ModalDipoleInfinity-final.log`, SHA256 `BFC8F1D0A485D0B55543A35492E31A810A4FEBB752D95121956B292936C9B4EA`. Exit receipt: `lean/logs/ModalDipoleInfinity-final.exit.log` = 0. Importable object: `lean/.lake/build/lib/lean/ModalDipoleInfinity.olean` (809896 bytes). Full check5 also exited 0. Root independent audit pending.

## Actual inverse-frequency polynomial

For inverse frequency w, the new literal finite polynomials in w are

`P(n,w) = -I + (n+1)/n*w + I*(n+1)^2/n^2*w^2 - (n+1)/n^2*w^3`,

`M(n,w) = -I*(n+1) + (n-1)*(n+1)/n*w + I*(n-1)^2*(n+1)/n^2*w^2 + (n-1)*(n+1)/n^2*w^3`.

`cPlus_factor` and `cMinus_inverse` derive from the actual `p_one`, `pMinus_one`, `pD_one`, and `pMinusD_one` formulas that cPlus_1(n,z)=(n−1)P(n,1/z) and cMinus_1(n,z)=M(n,1/z), for n≠0. The identities hold even for the totalized functions at z=0; no physical origin interpretation is attached to that totalization.

`scaledQuotient_actual` proves the exact identity (n−1) rationalPole_1(n,z)=−M(n,1/z)/P(n,1/z) for n≠0,1. It does not assume P is nonzero: division is totalized, and multiplication cancellation uses only n−1≠0. Separate local nonvanishing of P is proved.

## Genuine joint limit and uniform bounds

P(1,0)=−I and M(1,0)=−2I, hence the scaled quotient at (1,0) is −2. Both explicit polynomial functions are jointly continuous there, including the index denominators since n=1 is nonzero. Their quotient is jointly continuous because P(1,0)≠0.

`scaledQuotient_joint_limit` and `scaled_actual_joint_limit` apply to arbitrary source filters: as complex n→1 and 1/z→0, the actual scaled quotient tends to −2 (eventually n≠0,1). No root equation is used.

`scaledQuotient_bounds_near` gives one common joint neighborhood where the scaled quotient's norm is between 1 and 3. `actual_bounds_near` additionally proves cPlus is nonzero and transfers those bounds to ‖n−1‖ times the actual rational quotient norm. `real_actual_bounds` gives, for real n>1 sufficiently close to 1 and 1/z sufficiently small, actual cPlus≠0 and

`1/(n-1) ≤ ‖rationalPole 1 n z‖ ≤ 3/(n-1)`.

## Phase convention

`unitPhase z := z/(‖z‖ : ℂ)`. Its continuity at every nonzero complex number and invariance under positive real multiplication are proved. `real_actual_phase_limit` yields actual rational quotient unit phase tending to −1 as real n→1 from above and inverse frequency tends to zero. This is a unit-complex phase result, not continuity of the principal argument at the negative real axis.

## Scope

This repairs the joint-parameter modulus and phase input for an unbounded algebraic coincidence branch. It neither constructs such branches nor proves their analytic nonidentity/countability or all-degree modal isolation. All conclusions are independent of a determinant-zero premise. The imported frozen origin module and all other existing sources were preserved.

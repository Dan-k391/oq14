# Hankel coefficient bounds independent audit

Independent whole-source mathematical review and pinned compiler recheck by `fredholm_sol`: PASS.

- Source: `lean/HankelCoefficientBounds.lean`.
- SHA256: `3D8207807D9162CB27AEF00E02BF023AFA07E58A566808B7449D0E70AD0CDBBE`.
- Pinned Lean 4.19.0 independent `lake env lean HankelCoefficientBounds.lean`: exit 0, no warnings, all sixteen reports use only `propext`, `Classical.choice`, `Quot.sound`.
- Log: `lean/HankelCoefficientBounds.independent-fredholm.log`, SHA256 `94C7D1ADE41D332CC08C5DE29F32F213E96E1E6B184F808183EC38278662BFBA`.

The coefficient is the literal positive factorial ratio from the finite Hankel polynomial. The actual coefficient recurrence gives the reverse step; induction yields `t! * coefficient(l,l-t) <= coefficient(l,l)`. Reversing the finite sum therefore bounds it by the leading inverse-power term times the actual exponential series. All powers and denominators use positive real radius.

The actual derivative term norm equals `s/r` times its positive scalar term. Since the finite index satisfies `s<=l`, the derivative sum is controlled by `l/r` times the same already bounded sum. The outgoing phase and real-frequency exponential have unit norm, giving both asserted actual outgoing-function bounds. No asymptotic estimate or coefficient bound is assumed.

This review records the independent PASS completed before the second pause; exact source and preserved log hashes were reconfirmed on resume. Frozen source unchanged.

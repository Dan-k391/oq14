# Hankel intermediate bounds independent audit

Independent whole-source mathematical review and pinned compiler recheck by `fredholm_sol`: PASS.

- Source: `lean/HankelIntermediateBounds.lean`.
- SHA256: `D8E2574DF6C8B2E00A09159EE5EDFA7E4D779B8486B270A792A8400E9D12AA54`.
- Pinned Lean 4.19.0 independent `lake env lean HankelIntermediateBounds.lean`: exit 0, no warnings, all six reports use only `propext`, `Classical.choice`, `Quot.sound`.
- Log: `lean/HankelIntermediateBounds.independent-fredholm.log`, SHA256 `3A4869BEDF09BB746D67496971C3C57AC4CFEDBC18E5CAE341B44F0B5F27D6B2`.

The leading factorial coefficient satisfies the literal double-factorial recurrence and is bounded inductively by `(2l)^l`, including degree zero. For `q>=1`, `R>0`, `r>=R`, and `l<=2qR`, the actual ratio `2l/r` is at most `4q`. Its nonnegative logarithm permits replacing the integer exponent `l` by `2qR`, giving the stated leading exponential bound.

Combining that result with the previously proved actual finite-Hankel exponential estimate and `r<=2R` gives the exact exponent `(2+2q log(4q))*R`. The derivative bound also uses the proved `l/r<=2q`. Thus both estimates hold for the literal actual outgoing functions in every degree satisfying the hypotheses, without an assumed intermediate-range estimate. Frozen source unchanged.

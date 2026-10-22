# Genuine polynomially weighted reaction tails

Source: `lean/RadialHighOrderTail.lean`.

SHA256: `CCD63C15A63E82979D576FA8707E58C55FCCEBB94CFE4CC43E6684D50D908DCB`.

Author final compiler exit 0, no warnings; importable object 504064 bytes. All twelve selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialHighOrderTail-final.log`.

The actual high-degree estimate is factored into two powers of s/R. For R>=max(1,e*s) and l>=2R, one factor absorbs exp(3R/2), leaving exp(-R/2); the other is bounded by 2^(-l). Thus the literal actual finite-stack reaction term is bounded by 4*s^2*exp(-R/2)*2^(-l).

`reactionTerm` is the actual nonnegative coefficient norm times regular(l,s)^2 when R>0 and l>=C*R, and zero otherwise. `weightedTail` is its actual infinite sum against (l+1)^k. The polynomial-geometric comparison series is proved summable. The comparison test then proves the reaction series summable, rather than assuming its convergence or relying on the default value of a divergent sum. Its sum is bounded explicitly by

    4*s^2*exp(-R/2) * sum_l (l+1)^k*2^(-l).

For arbitrary degree weight k and inverse-power order N, the actual R^N-weighted tail tends to zero as R tends to infinity. The family assumptions are C>=2, fixed s>0, positive outer radius, and the actual per-layer algebraic barrier in the selected range. A separate common-stack geometry adapter discharges the barrier from actual Chain and common material/radius bounds.

This proves the radial scalar high-order tail. It does not identify a spatial Maxwell dyadic expansion or assume all-order physical Green convergence.

Status: author PASS and root full-source mathematical audit plus independent pinned compiler PASS (session 54030), exact hash unchanged; no warnings and all twelve reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 12 reports using only standard foundations. Final source SHA256 `ccd63c15a63e82979d576fa8707e58c55fccebb94cfe4cc43e6684d50d908dcb`. Independent log: `lean/logs/RadialHighOrderTail-root-audit.log`; log SHA256 `794bcfef64c8f4fe7fe533aaf038d9ef2819a5f27dc4e6251e4e5ec4cf2e1dac`. This certifies the stated scope, not either complete OQ14 construction.

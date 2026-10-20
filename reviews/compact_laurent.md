# Genuine convergent Laurent correction with finite-rank principal coefficients

Source: `lean/CompactLaurent.lean`.

SHA256: `550A1EA4F1736F0C44DD598A54CAB294A83D33F1CC9B4F14CFECDD27CF5506FA`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. The exported theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final complete-source audit passed at this exact hash. The source is frozen.

Actual finite-rank approximation supplies a fixed finite-dimensional Schur space at each center. The genuine finite-dimensional meromorphic inverse supplies a clearing power n. The analytic Woodbury numerator factors as U(z) C(z) V(z) through that fixed finite-dimensional space. The actual analytic-jet theorem proves finite rank of every Taylor coefficient of this numerator.

The theorem exports an actual analytic regular function G and a formal power series p whose every coefficient has finite-dimensional range. On a punctured neighborhood, the series with terms (z-z0) to the power j times p.coeff j, divided by (z-z0) to the power n, converges in operator norm to the actual inverse minus G. Thus its finitely many negative-power terms j<n have actual finite-rank principal coefficients. The expansion and coefficient ranks are proved conclusions, with no Laurent or finite-principal-rank premise.

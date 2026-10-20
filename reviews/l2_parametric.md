# Genuine L2 differentiation under a local derivative majorant

Source: `lean/L2Parametric.lean`.

SHA256: `E641525F836253C43713BB39E72536B3503B1F1BEFFEC4B3B1A3542E11E9AA04`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). Both theorem exports have axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

The helper first proves the literal integral formula for the squared L2 norm. Given pointwise complex derivatives and a uniform L2 majorant on a parameter neighborhood, the convex mean-value theorem bounds scalar difference quotients by that majorant. Squared quotient errors are bounded by four times its square. Pointwise derivative limits and dominated convergence make their integrals tend to zero. Actual almost-everywhere identities identify this integral with the squared norm of the quotient error of the L2 classes. Taking square roots proves a genuine Banach-space `HasDerivAt`.

The conclusion assumes neither L2 differentiability nor continuity. Root's independent final full-source audit passed at the exact hash above. The source is frozen.

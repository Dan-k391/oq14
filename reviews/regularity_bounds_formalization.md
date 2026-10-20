# Quantitative cutoff magnetic H1 bound

`lean/WeakPoynting/RegularityBounds.lean` is frozen at SHA-256 `3169e2e4f3733b39bb8dc69e154f471e4f25d6a51ebaebd97cdf6b69c220105e`. Direct compilation exited zero with four selected standard-axiom reports. Full output and source-scoped provenance are in `regularity-bounds-verification.txt` and `regularity-bounds-provenance.json`.

For an actual interior C2 cutoff χ satisfying `|χ| ≤ A` and each coordinate derivative bounded by B, regional weak Maxwell fields with permeability one, nonzero real frequency ω, and actual almost-everywhere coefficient bound `|ε| ≤ M` have constructed weak derivatives G of the zero-extended field χH satisfying

\[
\sum_{i,j}\|G_{ij}\|_{L^2}^2
\le 3\bigl(A|\omega|M\|E\|+2B\|H\|\bigr)^2
 +(3B\|H\|)^2.
\]

The vector norms on the right are the implementation's finite-coordinate maximum of component L2 norms. The left is the explicit sum of the nine squared component L2 derivative norms. This distinction is part of the statement and explains the factors three.

The proof first bounds the actual cutoff divergence, whose three terms are derivative multipliers. It then derives the magnetic curl norm bound directly from the actual Maxwell equation and the almost-everywhere permittivity bound. The previously proved zero-extension isometry and cutoff curl estimate bound both terms in the exact div–curl energy identity. No derivative of permittivity or trace/compactness premise is used.

This supplies quantitative local regularity for subsequent compactness work. It does not itself prove Rellich compactness, a trace theorem, or an observation-map bound.

# Continuous exterior response representatives

Frozen source: `lean/ExteriorContinuity.lean`.

SHA256: `DC49C994BDFBF98DB265C03E3BDD55E62DCE15A39BC996A8818E8D28D437B248`.

Pinned Lean 4.19 direct source compilation and olean emission passed on 2026-10-20. All nine exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

For an actual compact L1 source and a kernel continuous off the origin, the literal source integral is continuous at every point outside the source ball. A compact product of the observation neighborhood and source support supplies a uniform kernel bound. Dominated convergence is then applied to the actual integrand; no continuity of a chosen L2 representative is assumed.

The result applies to the ordinary dyadic electric response and the existing magnetic response. A countable rational-radius exhaustion upgrades the preceding almost-everywhere identification to the full open exterior. An explicit representative uses the ordinary integral there and the previous response elsewhere; it remains globally equal almost everywhere, while its exterior values are continuous and canonical among continuous representatives.

This module does not assert a radiation estimate or global classical regularity. It supplies the actual pointwise exterior representative to which a radiation theorem may apply.

Independent full-source reviews by the root and the modal agent both passed. They checked compact-product domination, countable rational exhaustion, actual global almost-everywhere preservation, and pointwise continuity of the exterior representative.

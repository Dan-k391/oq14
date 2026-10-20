# Actual Hessian action away from the point source

Frozen source: `lean/NewtonExterior.lean`.

SHA256: `28E1C51B2CBF7AE1EDC5D681C5A6C2F28C36449823C11C56A2EB91872F1E972E`.

Pinned Lean 4.19 direct compilation and olean emission passed on 2026-10-20. All seven exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The explicit radial Hessian is continuous off the origin. Compact tests avoiding the origin make its product integrable. Actual integration by parts twice identifies the ordinary Hessian with the full weak Hessian on precisely these tests. Translation gives the same statement at any excluded source point.

The full distributional Hessian retains its contact term in the earlier modules. This section removes no source contribution on tests meeting the source. Identification of the L2 response with the ordinary source integral on exterior regions is subsequent work.

Independent full-source audits by the root and the modal agent both passed. They checked the compact support exclusion, the two integration-by-parts signs and coordinate order, and the translated source exclusion. No substantive issue was found.

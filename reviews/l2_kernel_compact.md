# Actual compact convolution families from square-integrable kernels

Frozen source: `lean/L2KernelCompact.lean`.

SHA256: `872EC96E8783413E2A50E727F883145D20BF50480CBF3528F533E2B67BA2A270`.

Pinned Lean 4.19 source compilation and direct olean emission passed on 2026-10-20. All 14 exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The row at observation point `x` is the actual L2 function `q(x-y)`, constructed by measure-preserving composition. Its L2 norm is fixed, and its L2 translation orbit is continuous. The ordinary convolution is the actual bilinear L2 product with that row, giving both a Cauchy–Schwarz bound and a common continuity modulus for bounded source families.

Essential compact supports of kernel and source imply a common compact support of the continuous convolution representative. Arzelà–Ascoli gives precompactness in the supremum norm on that support. The previously constructed L1 convolution operator is identified almost everywhere with the representative before supremum-distance domination transfers compactness to its actual L2 output.

The final theorem proves genuine `IsCompactOperator` for convolution after any bounded linear input map whose outputs have a common compact support. No kernel derivative, compactness axiom, or assumed Hilbert–Schmidt representation is used.

Independent full-source audits by the root and the modal agent both passed.

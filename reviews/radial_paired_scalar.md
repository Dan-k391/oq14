# Actual paired TE/TM scalar series parity limits

Source: `lean/RadialPairedScalar.lean`.
SHA256: `72300532AA4860F938804649481505F590653D41AA8ACE3FD0C643A67943E86F`.

Author final compiler exit 0, no warnings; importable object 266392 bytes. All eight selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialPairedScalar-final.log`.

The proved actual parity ratios identify the limiting coefficient at every degree: -i*(q/sigma)^(2p) for even degree, -i*(sigma/q)^(2p) for odd degree. The proof uses the actual even/odd quotient results and natural degree parity; it introduces no coefficient-limit premise.

The actual common quarter-wave Segment list has literal material bounds from `RadialPairedFamily.pairs_parameters`, with q>=1 and 1<=sigma<=q^2. These bounds instantiate the genuine full compact uniform scalar series theorem. The limiting continuous-map series is genuinely summable. Its actual all-degree sum converges in compact supremum norm, for every fixed polynomial degree weight and mixed radial derivative order.

The TE specialization sigma=1 has even/odd coefficients -i*q^(2p) and -i*q^(-2p). The TM specialization sigma=q^2 swaps those coefficients. Both uniform limits use the actual untrimmed finite physical paired stacks at the proved sampled radii, whose early exceptional radius conditions disappear eventually. Analytic origin axes are included.

These are actual scalar radial series limits. The per-term derivative sums are not silently identified with derivatives of the summed kernel; that is proved in a separate differentiation successor. Spatial angular factors, Debye/vector reconstruction and physical normalization remain separate.

Status: author PASS; source frozen pending root complete-source and independent compiler audits.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `72300532aa4860f938804649481505f590653d41aa8ace3fd0c643a67943e86f`. Independent log: `lean/logs/RadialPairedScalar-root-audit.log`; log SHA256 `e708deb8a8e07f4269ba3ee65e0a372c52ebd371ee53bf2223737af35c7923f2`. This certifies the stated scope, not either complete OQ14 construction.

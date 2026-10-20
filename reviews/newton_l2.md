# NewtonL2 verification

Frozen source: `lean/NewtonL2.lean`.
SHA256: `9681B67130FF86461C375D501030E3AA8442CB9D26321BB94F7E84F9CA39EDB4`.

The pinned Lean 4.19 compiler completed cleanly on October 20, 2026. All 21
exported theorem reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; there are no admissions or additional axioms.

The source obtains scalar bilinear Parseval from the already constructed
Hermitian Plancherel equivalence by constructing actual conjugated Schwartz
tests. Actual measure-preserving coordinates transport the vector L2
projection. Its pairing with genuine Schwartz sources and tests equals the
negative of the actual iterated spatial Newton-Hessian integral proved in
NewtonConvolution. All finite integral sums use proved integrability.

The vector Schwartz range is proved dense from scalar density, the finite
product topology, and the actual component isometry. The spatial pairing
therefore determines a unique bounded L2 extension. This extension is
`newtonOperator = -physicalProjection`, with norm at most one.

This is an actual spatial-to-L2 identification on Schwartz sources and a
unique bounded extension to all vector L2. Direct weak spatial pairing for
arbitrary L1 intersection L2 sources is developed separately in NewtonL1L2;
it is not silently assumed here.

The hotspots agent independently read the complete source and accepted the
conjugation signs, measure transport, a.e. arguments, spatial action,
integrability, density and uniqueness on October 20. No substantive defect
was found.

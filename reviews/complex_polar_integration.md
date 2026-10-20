# Complex and Banach-valued Euclidean polar integration

Source: `lean/ComplexPolarIntegration.lean`.

SHA256: `0DCAC8C3E86CBCA43CAE89B466D5690EE5E17213B719EF27387B63B7B87449A1`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All eight exported theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final complete-source and compiler audits passed at this exact hash. The source is frozen.

The proved actual Euclidean polar measure-preserving homeomorphism transfers both the Bochner integral and integrability to the genuine sphere-times-positive-radius product. Fubini then reverses the order of integration. The actual positive-radius measure is its real Lebesgue subtype measure weighted by the squared radius, so the with-density integral and integrability identities yield the literal radial Jacobian and integrable radial moment. Explicit complex corollaries write real scalar multiplication as complex multiplication.

The general theorems apply to normed real modules; no completeness premise is needed. The integral formula and radial moment integrability assume actual spatial integrability. No polar formula, radial integrability, or PDE conclusion is added as a premise. Frozen `PolarIntegration.lean` is unchanged.

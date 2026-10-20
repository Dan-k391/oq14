# Scattering for the literal constructed device coefficient

Source: `lean/LayeredDeviceScattering.lean`.

SHA256: `BB714B00D4A958891C6A792CE243DA7525192B5409E43FDE558CC1E895D6E1E8`.

Author final compiler exit 0; importable object 534888 bytes. All 11 selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/layered-device-scattering-check.log`.

The coefficient in every conclusion is the literal finite indicator-sum coefficient constructed in `LayeredInclusionCoefficient`. The support radius is the actual outermost radial cut. The only material inputs are nonnegative prescribed contrasts, their explicit nonnegative common bound M, and exterior contrast zero. Exact dielectric values, their positivity, measurability, boundedness and compact support are proved by the constructor; none are supplied as agreement or support premises. The geometry inputs are the actual positive ordered cuts and separated positive-radius inclusions strictly inside the core. No partition, connectivity or uniqueness conclusion is assumed.

The actual real volume block is a unit at every positive frequency, its literal inverse solution satisfies the datum equation and is the unique volume unknown, and its actual physical incident solution satisfies dielectric Maxwell, all-ball L2, polarization, exterior continuity and the inverse-square Silver--Mueller defect bound. A classical vacuum incident-field wrapper is included.

The actual complex volume inverse has no exceptional point on the positive real axis and is analytic there as an operator and on fixed sources. An actual complex ball around each positive frequency consists of regular points. The existing real-axis identification with `MaterialField.solution` applies directly to this same constructed coefficient.

Scope is the explicit layered spherical inclusion geometry and nonnegative scalar susceptibility. These declarations do not prove arbitrary outgoing PDE-to-volume equivalence, full Maxwell pole isolation, or the completed channel theorem.

Status: author compiler PASS; ready for root independent full-source audit and compiler. Source held unchanged pending audit.

## Independent root verification on resumption

Full source reviewed; pinned compiler EXIT0. All 11 reports use standard foundations. Exact source SHA256 `bb714b00d4a958891c6a792ce243da7525192b5409e43fde558cc1e895d6e1e8`. Independent log: `lean/logs/LayeredDeviceScattering-independent-root.log`. The assumptions retain the stated scope and do not close the complete device construction.

# PhysicalDeviceFlux — author review, 2026-10-27

Author final PASS: pinned Lean 4.19.0, EXIT0, no warnings, five reports using only `propext`, `Classical.choice`, `Quot.sound`. Independent review is pending root verification.

- Source: `lean/PhysicalDeviceFlux.lean`, 161 lines; SHA256 `9B79CD69B1DFEC8FAF1691774E2A3D830F913A6B37D4B671F9FF0B0956D7F6CB`.
- Final log: `lean/logs/PhysicalDeviceFlux-final.log`; SHA256 `139C01F6D94B92541AE94BD62BEBC35D0DB0B33B84B8197860D4F13FF99D9068`.
- Exit receipt: `lean/logs/PhysicalDeviceFlux-final.exit.log`, value 0. Generated object exists.
- Complete source/log/object/receipt evidence: `reviews/physical_counted_normalization_author_2026_10_27.json`.

The electric and magnetic families are definitions of the existing literal piecewise device fields, using the proved TE background plus the inclusion's actual radiated series outside the core. `core_agreement` combines the actual `CoreMajorantDevice.coreMajorant_device` and actual radiated outside decomposition; no convergence, field identification, or integrability conclusion is assumed.

`unit_integrable_eventually` obtains the existing phase estimates from this agreement and the actual transmission parity identity. Rephasing both fields leaves their flux unchanged. The proved whole-plane L1 interface then gives integrability uniformly on the unit-physical-power sphere of any finite orthonormal span, eventually in the gain index and then the shell index.

`integrable_of_unit` extends the conclusion to the entire span: zero physical power forces the zero coefficient vector on that span; positive power is normalized by its inverse square root, and quadratic flux homogeneity transfers integrability back. `integrable_eventually` applies this to the actual device. `scaled_integrable_eventually` transports the result under the genuine plane dilation and its amplitude factor, using Haar-measure integrability under nonzero scaling.

This is an integrability companion to the existing finite physical-device construction. It does not assume integrability merely because a default-valued Bochner bypass integral satisfies an inequality. It gives no rates or uniform device size in the dimension. Source scan and final-newline checks pass; frozen dependencies remain unchanged.

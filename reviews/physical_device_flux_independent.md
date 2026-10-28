# PhysicalDeviceFlux — independent root audit

PASS, 2026-10-27. Complete source and mathematical scope reviewed independently of the author. Fresh pinned Lean 4.19.0 source compilation completed with exit 0. Source SHA256: `9B79CD69B1DFEC8FAF1691774E2A3D830F913A6B37D4B671F9FF0B0956D7F6CB`.

Audit log: `lean/logs/PhysicalDeviceFlux-root-audit.log`, SHA256 `139C01F6D94B92541AE94BD62BEBC35D0DB0B33B84B8197860D4F13FF99D9068`. Exit receipt: `lean/logs/PhysicalDeviceFlux-root-audit.exit.log` = 0. All 5 selected reports use only `propext`, `Classical.choice`, and `Quot.sound`; no warnings, errors or proof placeholders. This re-elaborated the source against existing dependency objects, not a clean dependency rebuild.

The actual finite-device field is used throughout. Core agreement and outside radiated decomposition supply the phase estimates, which give whole-plane flux integrability on the unit-power sphere. Zero power forces the zero vector; positive power normalization and quadratic flux scaling extend integrability to every vector of the chosen span. Nonzero plane dilation preserves the result. No default-valued integral is used to infer integrability.

# Actual material self-consistency

Frozen source: `lean/MaterialField.lean`.

SHA256: `0981916B804BB148F2F6BC86C87A5DF873F5DCDC58F5DA5B57A730C5BB998B40`.

The pinned Lean 4.19 compiler completed successfully on 2026-10-20. All seven exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The source is the actual square-root-weighted volume unknown. Its compact support and the actual scattered electric field's local L2 regularity are proved. The exact spatial volume equation implies `rho = chi * (incident + scattered)` almost everywhere, including the zero-contrast set. The proof multiplies by the real nonnegative square root and never divides by the contrast.

The concrete inverse from `DynamicVolume` solves the volume equation, so the same material relation holds for its solution whenever the established error bound is below one.

The incident field may be defined on all physical space. The theorem assumes an actual L2 weighted datum with the displayed almost-everywhere equality to `sqrt(chi) * incident`. It does not assume that the incident wave is globally L2. Construction of that datum from local incident regularity is a separate step.

Hotspots independently read the entire source and accepted its actual support, spatial response, and material algebra. This module supplies self-consistency to the separate Maxwell source/PDE assembly; it does not itself claim a radiation condition.

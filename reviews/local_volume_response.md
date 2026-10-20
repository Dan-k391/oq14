# Actual local L2 electric response

Frozen source: `lean/LocalVolumeResponse.lean`.

SHA256: `A1D8DD71CEE981386F1109AA51BBE463BE330ACF9E0977921428B8BED548C183`.

The pinned Lean 4.19 compiler completed successfully on 2026-10-20. All seven exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.

For an actual L2 vector source whose coordinate functions agree almost everywhere with compactly supported L1 source densities, the literal electric field defined in `FieldResponse.electric` is L2 on every observation ball. This is proved by exact agreement there with the global L2 vector `NewtonL2.newtonOperator F + DynamicConvolution.operator k (R+S) F`. The cutoff at the sum of the observation radius R and source radius S is exact, with no approximation.

The global representative has norm at most `(1 + 9*entryMass k (R+S))*norm F` when `R+S` is nonnegative. Actual component local integrability follows from finite-measure L2 to L1 and arbitrary compact containment in a ball.

Hotspots independently audited the complete source and found no defect. The source assumptions concern the actual densities and their actual L2 representative; no response agreement, local energy bound, or PDE conclusion is assumed.

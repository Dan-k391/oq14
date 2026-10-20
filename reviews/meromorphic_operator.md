# Bounded-linear and composition transfer of actual meromorphy

Source: `lean/MeromorphicOperator.lean`.

SHA256: `EBA4387A3A09E3F5E1D3894A1FC3178C5CF8E79F8B57841015FCEECE2EE9CAD3`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. Both exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent final full-source audit passed at this exact hash. The source is frozen.

A continuous complex-linear map commutes with the actual scalar pole-clearing power. For composition of operator-valued meromorphic maps, the sum of their actual clearing exponents clears the composition, and bounded bilinear composition preserves analyticity of the cleared factors. These are proved from the definition of Banach-valued meromorphy and actual bounded maps, without a composition-meromorphy premise.

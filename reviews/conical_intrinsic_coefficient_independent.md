# ConicalIntrinsicCoefficient — independent root audit

PASS, 2026-10-27. Complete source and mathematical scope reviewed independently of the author. Fresh pinned Lean 4.19.0 source compilation completed with exit 0. Source SHA256: `39047D9EDFEE2E4BDCDAC45FF09340817D7A6975D4D3188CE14DDCCB22FFCF0E`.

Audit log: `lean/logs/ConicalIntrinsicCoefficient-root-audit.log`, SHA256 `AC1C218402F2326FE0598ADA3209B9861694CC79F94B25DB75C98704477F630C`. Exit receipt: `lean/logs/ConicalIntrinsicCoefficient-root-audit.exit.log` = 0. All 8 selected reports use only `propext`, `Classical.choice`, and `Quot.sound`; no warnings, errors or proof placeholders. This re-elaborated the source against existing dependency objects, not a clean dependency rebuild.

The coefficient is chosen from the actual projected expansion and proved unique. The total tangential moment has this coefficient times r^nu plus an O(r) remainder. Actual local-field additivity gives moment additivity using polar almost-everywhere transfer and integrable angular products. Since 0 < nu < 1, a nonzero residual coefficient cannot be hidden in the O(r) error. Scaling and addition therefore depend only on the actual field, not the auxiliary gauge choice.

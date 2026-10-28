# CompactFieldDatum — author verification

Author PASS, 2026-10-27. Source `lean/CompactFieldDatum.lean` SHA256 `6345EF58343BCE6F1661EA13B7CBA1EECC0CA4C1FCBA26DF35F33BB885B93654`. Fresh pinned Lean 4.19.0 object compilation: exit 0, nine axiom reports, no errors or warnings, only `propext`, `Classical.choice`, and `Quot.sound`.

Final log: `lean/logs/CompactFieldDatum-author-final.log`, SHA256 `4EED189F2036C3DBBEF4DBB82C1C59691FD9F7F298DA51E2C3B4F71C6F98B612`. Exit receipt: `lean/logs/CompactFieldDatum-author-final.exit.log` = 0.

The core is the closed unit ball in physical space. The scalar map is a bounded complex-linear operator from continuous complex fields on that compact core to physical scalar L². Its representative agrees almost everywhere with the explicitly defined zero extension, which equals the input on the core and zero outside. The proof uses compact support and a uniform-norm bound, followed by an L² comparison with the unit indicator. The construction is unconditional and introduces no custom axioms or placeholders. No vector or weighted-field identification is asserted here.

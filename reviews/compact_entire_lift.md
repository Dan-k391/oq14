# CompactEntireLift — author verification

Author PASS, 2026-10-27. Source `lean/CompactEntireLift.lean` SHA256 `31327AD9844F9484CC8BC113125C013CCDEEE8E61D4C8E23B509F9AB015CEC9B`. Fresh pinned Lean 4.19.0 object compilation exited 0, with two axiom reports, no errors or warnings, and only `propext`, `Classical.choice`, and `Quot.sound`.

Final log: `lean/logs/CompactEntireLift-author-final.log`, SHA256 `3DF258FDE5A55B0A03F916B7EA8A52AF8BF2E7CD7B242DEDF6FE0E1A98BA8690`. Exit receipt: `lean/logs/CompactEntireLift-author-final.exit.log` = 0.

For compact Hausdorff X, continuous r : C(X, ℂ), and an entire scalar f expressed by Differentiable ℂ f, the lift k ↦ (x ↦ f(k r(x))) is analytic at every complex k as a C(X, ℂ)-valued function in the uniform norm. The proof uses continuity of the uncurried map, the Banach-valued Cauchy integral power series, and evaluation by continuous linear maps to identify it with the scalar Cauchy formula locally. It does not assume that pointwise analyticity alone implies Banach-valued analyticity. No placeholders or custom axioms are introduced.


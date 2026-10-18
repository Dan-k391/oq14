# Verified cutoff bridge

`HCurlCutoff.lean` imports the existing `HCurlDomain` module and proves localization facts for its actual restricted-measure complex L² fields. It does not change the toolchain or introduce a new analytic axiom.

For a compactly supported globally C¹ complex scalar χ, `multiply` represents χE almost everywhere. `productCurl` is the coordinate formula

`χ C + grad χ × E`.

`OQ14.CurlCutoff.weakCurl_multiply` proves that if C is the distributional curl of E on Ω, this expression is the distributional curl of χE. The proof multiplies compact C¹ tests, applies the already proved classical product rule only to those tests, and rearranges genuine Lebesgue pairings. Neither E nor C is assumed differentiable. L² membership of χE and every derivative product is proved using the boundedness of continuous compactly supported functions.

`OQ14.CurlCutoff.cutoff_norm_le` proves, in the existing maximum coordinate graph norm,

`‖cutoff χ u‖ ≤ (A + 2 B) ‖u‖`,

provided A and B are nonnegative, `|χ(x)| ≤ A`, and every coordinate derivative satisfies `|∂ᵢχ(x)| ≤ B`. These explicit derivative bounds are hypotheses for this quantitative estimate. The multiplier's L² membership and weak product formula do not require the caller to provide the bounds.

`OQ14.CurlCutoff.weakCurl_cutoff_extend` proves the whole-space weak curl relation after zero extension when Ω is open and `tsupport χ ⊆ Ω`. The extension is an actual L² class represented by the indicator of Ω. `extendScalar_norm` proves preservation of its L² norm, and `extendScalar_pair` identifies whole-space test pairings with the restricted-domain integral. The global result is tested against arbitrary whole-space compact C¹ functions; their products with χ have support inside Ω. No boundary condition is assumed on the original field.

The source does not prove a boundary trace theorem, unrestricted zero-extension theorem, existence of smooth cutoffs for arbitrary geometric pairs, density or smoothing of H(curl), restriction between two domains, or a Maxwell solution existence theorem. It supplies the multiplication and interior zero-extension steps those later developments can use.

The final standalone command was `lake env lean HCurlCutoff.lean` from `D:/oq14/lean`, using the project's existing Lean 4.19.0 environment and already built imported modules. It exited 0 with no warnings. `verification.txt` contains the complete returned compiler output; `provenance.json` records the compiler, command, source/dependency hashes, and scope. All eleven printed exported theorem dependency lists contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The coordinator's combined build should register and check this module alongside the other project modules.

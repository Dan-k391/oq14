# Saved draft checkpoint: NewtonConvolution

Checkpoint requested by the user; no further proof work was started after saving this state.

## Frozen dependencies

- `lean/HeatFourier.lean`: 26 exports, clean compiler/standard-only axioms, independently reviewed by root and hotspots. SHA256 `61F2183591214739868C469247FEE6255D30C0C5795DBF1A7C6BAE86885CA3DC`.
- `lean/NewtonFourier.lean`: 11 exports, clean compiler/standard-only axioms, independently reviewed by hotspots; root built its olean. SHA256 `DB7F04A6F115631931A2D33D050442318EDD0D9B8BA32F32D02E961C34CC9F17`.
- `lean/NewtonHessian.lean`: 10 exports, clean compiler/standard-only axioms, independently reviewed by root and hotspots; root built its olean. SHA256 `A6719B49C0F35E32AA080DFFDFE194C7722054F61C3E3622582DB23BF6415244`.

These establish the actual Newton Schwartz-pairing Fourier identity; the full weak Hessian symbol, including the exact source trace `Delta N=-delta`; and equality of that matrix with the negative physical longitudinal Fourier multiplier. They do not yet establish the explicit spatial convolution action on sources.

## Draft only

`lean/NewtonConvolution.lean`, SHA256 `BF697077BAD9D0E58B72FBE8430E95104D071B1FB5C01DFF767442DBF01AB590`, is unregistered and unverified as a whole. No axiom-print block or independent audit has been completed for it. Do not include it in a verified release yet.

The draft defines actual translated Schwartz tests `f(x+y)` and the spatial weak response `integral rho(y)*weakHessian(translate y f)dy`. It contains the intended proof of the multiplier identity for every actual L1 source rho, using absolute Fubini. The translated inverse-Fourier phase is `exp(-2*pi*i*inner(y,xi))`, as required. No Maxwell conclusion is supplied as a premise.

Final compiler invocation: session 30581, exited with code 1. No compiler sessions remain active for the channels agent. Three errors remain:

1. Line 46, `translate_pderivative`: `rw [fderiv_comp ...]` fails to recognize the lambda as the composition with `fun z => z+y`. Resolve with an explicit composition `change`, or use the composed `HasFDerivAt` proof and its `fderiv` equality. The derivative is the identity map.
2. Line 69, `weakHessian_translate_spatial`: the `integral_add_right_eq_self` invocation leaves its measure implicit, causing `Measure.IsAddRightInvariant` to be stuck. Supply `(μ := (volume : Measure Space))` explicitly.
3. Line 106, `source_fourier_pairing_integrable`: `simp only [norm_mul, HeatFourier.phase_norm, one_mul]` reports no progress. Inspect the goal after `filter_upwards`; the domination target likely already has those forms reduced. Remove the redundant simp or use an explicit `change` before the product norm inequality. The intended bound is `|rho(y)|*|hessianSymbol|*|phase|*|inverseFourier f| <= |rho(y)|*|inverseFourier f|`, using the proved symbol norm bound and unit phase norm.

Suggested resume order: fix the three local elaboration issues; recompile this file only; add a meaningful spatial-pairing integrability statement if needed; request independent review; append exact public axiom reports; freeze hashes before registration. Then connect the resulting actual L1 spatial weak convolution identity to the physical L2 projection on Schwartz sources and extend only through proved density/continuity. Do not define the spatial convolution by its multiplier or assume that remaining identification.

Compile command from `D:\oq14\lean`: `D:\oq14\.tools\lean\lean-4.19.0-windows\bin\lake.exe env lean NewtonConvolution.lean`.

No Git commands were used. Frozen sources and build configuration were not edited. Root separately owns the point-singularity integration-by-parts bridge for the dynamic remainder.

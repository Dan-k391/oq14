# Saved resumption checkpoint: weak div–curl regularity

Work was paused at the user's checkpoint request. All source is saved. No compiler sessions or background proof jobs remain active. Do not change frozen sources, dependency pins, build configuration, or ledgers without coordinating with the parent agent.

## Frozen result

`lean/WeakPoynting/DivCurl.lean` directly compiles with six standard-axiom audit reports. SHA-256: `20c03d9adf1778f494abd6222d0c8eebdab03100bfe7d0fa7c69301c7a24c3cb`. Evidence: `divcurl-verification.txt`, `divcurl-provenance.json`; scope: `reviews/divcurl_formalization.md`. Its olean exists in the ignored local build cache. It is not yet a parent-reviewed combined-release result.

The previously frozen WeakPoynting family through `EnergyLocalization.lean` is unchanged. The exact latest Aperture, Axial, and LipschitzBoundary hashes are those in their current provenance files, after the authorized `constant` to `lipschitzBound` field rename.

## Saved draft and current compiler errors

`lean/WeakPoynting/DivCurlCompact.lean` is a saved, unregistered draft. The first direct compilation exited one. Do not include it in a verified release or count its audit output as proved exports. There are three proof errors:

1. Line 35, `divergence_smoothField`: the reflected-test identity has sign opposite to the final goal. The current `linear_combination hh` should be tested with `linear_combination -hh`. This is a proposed repair, not a verified result.
2. Line 75, `embed_curl_smoothSchwartz`: `rw [hx, hy, ...]` cannot find the syntactic `MemLp.toLp` term from `hy` because the goal still contains `mollifyL2`. Unfold/change `mollifyL2` in the goal, or first give `hy` an explicitly matching `mollifyL2` statement, then rewrite.
3. Line 85, `embed_divergence_smoothSchwartz`: the same definitional rewrite issue.

The current compile already accepted the compact-representative convolution-support proof, Schwartz weak-partial integration-by-parts proof, and weak-partial closedness proof. This is diagnostic progress only; the whole draft has not compiled cleanly. Error recovery produces `sorryAx` in dependent audit output, so that failed output must not be treated as evidence.

The draft defines genuine distributional divergence and partial derivatives using existing continuous L2 test functionals. It constructs actual compactly supported smooth convolutions as Schwartz fields, identifies their L2 embeddings, and aims to prove simultaneous strong approximation of the field, curl, and divergence. Compact support is required of an actual representative of each L2 component, not of arbitrary default values of an equivalence class.

## Next proof steps after resumption

1. Repair the three errors and obtain a clean direct compile of the existing draft.
2. Apply `DivCurl.schwartz_divcurl_energy` to differences of two approximants. Prove a coordinate derivative estimate such as `norm(derivative(f)-derivative(g)) ≤ 2 * max(norm(curl(f)-curl(g)), norm(div(f)-div(g)))`, using the finite coordinate max norm and the three curl terms.
3. Strong convergence of the actual mollified curl and divergence then makes each of the nine derivative sequences Cauchy. Use completeness of actual scalar L2 to obtain nine limits.
4. Pass the genuine compact-test identity to those limits using the draft's `weakPartial_limit`. The resulting theorem should require only actual compact L2 representatives and actual L2 weak curl/divergence, and conclude existence of all nine actual L2 weak derivatives. It must not assume H1 regularity or a desired PDE estimate.
5. Pass the finite sum of squared norms to the limit to obtain the exact div–curl energy equality for those weak derivatives.
6. In a separate later module, derive local magnetic H1 regularity for regional weak Maxwell fields: obtain weak magnetic divergence zero from the existing divergence-of-curl theorem for nonzero frequency and constant permeability, combine the actual cutoff curl formula with an independently proved divergence cutoff formula, extend the interior cutoff by zero, and apply the compact theorem. This step is not yet implemented.

## Reproduction environment

Working directory: `D:/oq14/lean`. Toolchain: `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`; prepend its directory to PATH. Run `lake env lean WeakPoynting/DivCurlCompact.lean`. To emit the frozen dependency olean, use `lake env lean -o .lake/build/lib/lean/WeakPoynting/DivCurl.olean WeakPoynting/DivCurl.lean`. Existing pinned mathlib and caches suffice; no additional download is currently known to be necessary.

The final frozen capture script is retained under ignored `tmp/record_divcurl.py`. It generated the actual checked-in text evidence and provenance; preserve the evidence files, not toolchain or cache directories. Completed compiler session IDs were 83121 (frozen DivCurl, exit zero) and 55396 (draft DivCurlCompact, exit one); both have been consumed and closed.

## Independent review delivered

`reviews/kernel_estimates_independent.md` records the read-only passing audit of the parent's frozen KernelEstimates module. Its last bound is correctly entrywise, not already an operator-norm estimate. No parent files were edited.

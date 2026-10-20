# Exterior smoothness: actual compact-source integral responses

`lean/ExteriorSmooth.lean` is frozen with 9 checked exports.

SHA256: `42483008985633e3bf20809bbe4c474f2cef854428910034fcddd22964b5abbd`.

The generic theorem proves C∞ regularity of the literal convolution response outside a source ball for every integrable complex source supported in that ball and every kernel smooth away from zero. It constructs an actual compact smooth cutoff equal to one on the compact difference set of a neighborhood of the observation point and the source ball. The cutoff vanishes near zero, so its product with the singular kernel is globally smooth and compactly supported. Mathlib's proved smooth-convolution theorem applies to this kernel and the L1 source, and pointwise support gives local equality with the original response.

The specializations prove actual C∞ regularity of the scalar outgoing response, the ordinary dyadic electric integral, and the magnetic gradient integral. Smoothness of the gradient and Hessian kernels is proved from their explicit formulas away from zero. No regularity of the source, no derivative-under-integral premise, and no field smoothness assumption is introduced.

The theorem concerns the actual ordinary exterior representatives. Their equality almost everywhere with the global L2/distributional electric response remains supplied by the previously frozen `ExteriorContinuity` and `NewtonExteriorResponse` chain. This file does not by itself assert classical Maxwell equations or uniqueness of a scattering solution.

Direct compiler output is in `lean/exterior-smooth-verification.txt`; `lean/exterior-smooth-provenance.json` records the exact compiler, manifest, recursively imported local source hashes, and capture provenance. Compilation and olean generation both returned exit code 0. All 9 exported theorem reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The coordinator and the hotspot agent independently read the complete source; both audits passed.

# Complementary local Maxwell estimates

`lean/WeakPoynting/MaterialCaccioppoli.lean` is frozen. All eight selected exports cleanly compile with only `propext`, `Classical.choice`, and `Quot.sound`. Independent full source reviews by the coordinator and the hotspot agent both passed.

Source SHA-256: `1019802381705ebe88b9324cb8521ecc58468b27a44a1cb8c40e987375a9ab9a`.

The main estimate is derived from the actual regional weak Maxwell energy balance:

`∫ ζ² |H|² ≤ 2 ∫ ζ² ε |E|² + (4/ω²) ∫ |∇ζ|² |E|²`.

The proof establishes the swapped-field reactive-flux identity and applies the already proved Young inequality with frequency −ω. All integrability is established before passing to integral comparisons. No positivity or smoothness of ε is required for this estimate; the graph equations supply integrability of the weighted material energy.

The actual graph equation `curl E = iωH` then gives:

`∫ ζ² |curl E|² ≤ 2ω² ∫ ζ² ε |E|² + 4 ∫ |∇ζ|² |E|²`.

For `|ζ| ≤ 1`, `|∇ζ|² ≤ d²`, an outer cutoff χ equal to one on the support of ζ, and ε ≤ M with M nonnegative, the module derives magnetic energy and norm bounds from the outer electric energy. Its final result bounds the sum of the local electric and electric-curl energies by `(1 + 2ω²M + 4d²)` times the outer electric energy.

The local curl quantity is ζ times the genuine weak curl of E. It is not identified with the curl of ζE. There is no boundary trace, coefficient derivative, positive dielectric lower bound, or global scattering-field L2 premise.

Complete direct compiler output and dependency hashes are saved as `lean/WeakPoynting/material-caccioppoli-verification.txt` and `lean/WeakPoynting/material-caccioppoli-provenance.json`; the compiled olean is available locally.

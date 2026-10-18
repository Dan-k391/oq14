# Actual weak Maxwell energy and Caccioppoli audit

Frozen source: `lean/WeakPoynting/Energy.lean`, SHA256 `b755c84e82b73ab9892cb67616ef6adab30768463474d8e1b0e5b66ac99942d5`. All ten selected exports compile without warnings or errors and report only `propext`, `Classical.choice`, and `Quot.sound`. There are no admissions or custom axioms. Direct compiler output and exact source/dependency hashes are in `energy-verification.txt` and `energy-provenance.json` beside the source.

`weak_energy_identity` is the imaginary part of the previously proved local complex Poynting identity for actual regional H(curl) fields satisfying the actual a.e. Maxwell curl equations. The material coefficients in this identity are arbitrary real functions. Its combined integrand is independently proved integrable. The real and imaginary complex-product signs are checked by exact coordinate algebra; the identity is not a hypothesis in a physical structure.

For permeability one and nonzero real frequency, `weighted_electric_integrable` derives integrability of `χ ε |E|²` from that integrable density, the L2 magnetic energy, and the actual cutoff/cross-product term. No separate bound or measurability assumption on ε is used: the a.e. curl equations already constrain its products with the fields. `weighted_energy_balance` then separates the genuine integrals and proves

`ω ∫ χ ε |E|² = ω ∫ χ |H|² + ∫ ∇χ · Im(E × conjugate(H))`.

The vector inequality is also proved, rather than postulated. `real_cross_energy` gives the exact real-gradient/complex-vector Lagrange identity. Nonnegativity of the energy of `ω m ζ E + 2 i (∇ζ × H)` gives the scaled Young inequality. This fixes the reactive-flux sign and yields the standard constants without an unproved pointwise cross-product estimate.

Applying the actual weak identity to the squared compact C1 cutoff and integrating the scaled pointwise inequality gives `OQ14.WeakEnergy.caccioppoli`:

`∫ ζ² ε |E|² ≤ 2 ∫ ζ² |H|² + 4/(ω² m) ∫ |∇ζ|² |H|²`,

for ε≥m>0 a.e. All terms are proved integrable before integral monotonicity or splitting. The proof allows any nonzero real frequency, uses regional L2 field/curl classes, and needs no derivative or upper bound of ε. The actual dielectric problem with bounded positive ε is included. The scalar cutoff is compact C1 with support inside the open region; a Lipschitz energy-cutoff extension is not asserted by this module.

This proves the weighted local Maxwell energy estimate, not magnetic H1 compactness, scattering existence, a boundary trace theorem, or a final channel count. A separate support-localized corollary converts it to the manuscript's electric-to-magnetic energy estimate using a cutoff equal to one on the inner set and bounded gradient.

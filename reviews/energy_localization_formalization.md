# Support-localized Maxwell energy audit

Frozen source: `lean/WeakPoynting/EnergyLocalization.lean`, SHA256 `31e508428c21f9c797af8b82c325aa7aef7d0f6a3649db24673f290aebdc4dc5`. Four selected exports compile cleanly and report only `propext`, `Classical.choice`, and `Quot.sound`. Complete directly captured compiler output and source/dependency hashes are in `energy-localization-verification.txt` and `energy-localization-provenance.json` beside the source. There are no admissions or custom axioms.

`gradient_zero_off_support` uses the actual Frechet derivative of a function vanishing on a neighborhood outside its topological support. It is not a support axiom for a weak derivative. The resulting cutoff and derivative support facts yield `cutoff_energy_support_bounds`: for |ζ|≤1 and |∇ζ|²≤d², the weighted magnetic energies are bounded by the actual L2 energy on the cutoff support, with constants one and d².

`electric_energy_on_unit_region` proves integrability of ε|E|² on an inner measurable set K where ζ=1, using the weighted integrability already derived from the actual Maxwell equations. Its comparison with the full weighted energy uses the a.e. nonnegativity of ε, and all indicator integrals are genuine integrable functions. No unbounded material-energy integral is split before its integrability is established.

The main theorem `OQ14.EnergyLocalization.maxwell_local_electric_energy` combines these comparisons with the proved Caccioppoli inequality to give

`∫K ε |E|² ≤ [2 + 4d²/(ω²m)] ∫supp(ζ) |H|²`,

for ω≠0, ε≥m>0 a.e., a compact C1 interior cutoff ζ equal to one on K, |ζ|≤1, and the actual gradient bound. This is the electric-to-magnetic energy estimate in the manuscript's Caccioppoli lemma, with its stated constants. The result uses the regional measure explicitly; the cutoff support lies inside the open region, and the unit-cutoff condition also forces K inside that region. No coefficient upper bound or derivative, field differentiability, scattering solvability, or boundary trace is assumed.

This does not yet prove the subsequent flux-domination inequality, magnetic H1 regularity, or channel-dimensional estimate. Those are distinct analytical bridges.

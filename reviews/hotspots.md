# Hotspot derivation and independent channel review

Date: 17 October 2026, America/New_York. This is an audit record, not a competing mathematical manuscript. Canonical statements and proofs are in `manuscript/sections/hotspots.tex` and `manuscript/sections/channels.tex`.

## Hotspot result and scope

- **PROVED, hs:packing:** For fixed positive frequency and any strict ordinary dielectric contrast, any finite number of arbitrarily high, arbitrarily narrowly localized electric peaks can be placed in an arbitrary open cross-sectional patch, with one physically normalized Herglotz input and smooth binary interfaces. Physical normalization is incoming power per invariant length. The actual object is infinite in the invariant direction.
- **PROVED, hs:coefficient:** An exact finite-frequency angular-projection formula supplies a continuous singular coefficient. The coefficient is continuous in local L2 on the solution space; no asserted full pointwise corner expansion is needed.
- **PROVED, hs:local-excitation / hs:runge / hs:simultaneous:** Small-radius Dirichlet matching proves local nontriviality at the fixed frequency. The total-field Runge proof uses outgoing-source mixed reciprocity, exterior uniqueness, and propagation across finite flat interfaces. One finite-union-of-kernels argument supplies a single illumination for all peaks.
- **PROVED, hs:rounding-convergence:** A common exterior DtN formulation, uniform Gårding inequality, compactness contradiction, and dominated coefficient convergence prove strong H1 convergence under inward rounding. Fixed flat-interface regularity supplies one-sided C1 convergence on observation collars. No estimate uniform near the moving rounded tips is assumed.
- **PROVED, hs:regional-ratio:** Bounded-region energy remains bounded while each selected peak tends to infinity along rounding. This is not a modal volume.
- **OPEN, hs:open3d:** Finite-height vector-Maxwell realization and normalized modal packing require additional bridges. No 2D-to-finite-3D or driven-to-modal inference is claimed.

## Self-audit

The exact identities checked were the TM signs, the four-sector transfer-matrix determinant and trace, the angular exponent, variation-of-constants signs and factors, the local L2 continuity of the coefficient formula, exclusion of the negative radial power by H1 regularity, and physical Herglotz incoming-power normalization. For constant radial forcing F=1, the displayed particular solution reduces to `-k^2 r^2/(4-alpha^2)`, as required by the radial differential operator.

The rounding proof was checked against the failure of operator-norm convergence for changing principal coefficients. It uses no such convergence: only `(a_rho-a) grad z -> 0` for a fixed test and `(a_rho-a) grad u -> 0` for the fixed limiting solution. Uniform inverse norms follow by a separate normalized compactness contradiction. The theorem retains one incident field throughout rounding and allows coefficients to become arbitrarily small after physical normalization.

The topology of the sharp reference geometry was checked explicitly: the two dielectric squares at each selected point touch only at a vertex. Unique continuation crosses open flat interfaces along paths avoiding the finite vertex set. Rounding inwards separates closures and gives smooth binary interfaces. All field comparisons used to preserve peaks occur at fixed ordinary points and collars away from changed vertices. The peak definition takes the maximum of the one-sided interface limits and uses a whole collar as a separating barrier.

The root reviewer and the independent counterexample reviewer identified the same wording error in the DtN Gårding paragraph: a finite **upper** bound on real DtN multipliers is needed because the form contains minus the DtN map. This was corrected. Differential-measure typography was also repaired. The counterexample reviewer found no substantive mathematical gap after checking the local coefficient, fixed-frequency matching, total-field Runge argument, physical normalization, rounding, and simultaneous collar bounds. Its suggested explicit derivative formula for the radial particular solution was added as hs:particular-derivative.

## Independent review of the channel section

Read-only review of `manuscript/sections/channels.tex` checked:

1. `ch:fluxlemma`: the Hermitian cross-Poynting divergence cancels for real symmetric permittivity; the transverse derivative and the sign of the volume-flux formula are correct. The argument uses a legitimate weak flux and retains the lateral contribution.
2. `ch:magneticHone`: divergence-free magnetic fields and the curl/div Fourier identity produce the stated uniform H1 estimate. The direct-sum Minkowski argument gives exactly `C_H = k0^2 eps_plus + d1^2`.
3. `ch:caccioppoli`: the Young-inequality constants give exactly `C_E^2 = 2 + 4 d2^2/(k0^2 eps_minus)`. The flux domination factor K has the correct factors of 2 and material normalization.
4. `ch:resourcecount` and `ch:average`: the box count is an exact lattice-cell inclusion, not a Weyl asymptotic. The component multiplicity factor, Gram-matrix normalization, trace comparison, and integral lower bound on the eigenvalue sum check out.
5. `ch:fulloutput`: the finite-rank approximation uses the complete transmission map and the orthogonal complement of the kernel of a bounded finite-rank field projection. Passage and bypass apply to every residual vector. The next eigenvalue strictly exceeds the cutoff, giving the required strict approximation error. The unknown full-field resource remains explicitly present.
6. `ch:arearesource`: substitution of `r = 1/(k0 sqrt(eps_plus))` gives the displayed coefficient and area dependence; shape, collar, thresholds, material ratio, and dimensionless `omega B_*` remain explicit.
7. `ch:anisotropy`: real symmetry gives the cross-Poynting cancellation, and the positive tensor quadratic form yields the stated extension. Constant scalar permeability remains a necessary hypothesis of this proof.

No substantive channel-section error was found. One wording issue was sent to the channel author: the section-compatibility assumption initially defined the flux density only on the support of the window but integrated it over the whole plane outside D. The author corrected it to specify a density on the entire section plane with the required integrability. This change does not alter the theorem.

The channel verdict remains **OPEN** without the uniform field resource or a replacement uniform approximation theorem. None of the reviewed algebra, local regularity, or rounded hotspot construction supplies that missing family estimate.

## Primary-source checks

The versioned tutorial, Costabel--Dauge--Nicaise (1999), Zhao--Zhang--Miller (2020), and the publisher's record for Ochs (1989) were inspected through primary source pages. Costabel's bounded-domain interface results are used only for context; the hotspot proof supplies its own exact scalar projection and global transmission argument. Ochs is background for the approximation strategy and is not treated as a ready-made material-dependent Runge theorem.

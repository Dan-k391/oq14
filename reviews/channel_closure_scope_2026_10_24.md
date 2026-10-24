# Channel closure: exact remaining Lean obligations (author scope note, October 24)

Author scope note by the channel proof agent. It records what the Lean tree proves today for obligations (i) to (v) and the smallest missing theorem for each, then ranks them by feasibility. Statements marked "proposed" are NOT compiled. All other statements are copied from lean/*.lean at the time of writing. Nothing here upgrades a manuscript PROVED label to a Lean verified one, and no premise is to be supplied as an axiom. Source/CLAIMS rows consulted: ct:profile, ct:jets, ct:gram, ct:model, ct:completion, ct:gap, cl:kernelbounds, cl:planebounds, cl:remainder, rg:physical-limit, ca:powerbudget, uc:counterexample, cb:*, nr:*.

## What was attempted (one item)

Of the obligations, the one judged most feasible and fully inside my area was the "section wrapper" the October 23 adapter note (item 3) says is missing: turning the sup-norm unit polydisc of `RestrictedTETotalLinear.uniform_actual_inverse_to_dipoles` into the actual physical-power unit ball of a constructed orthonormal input space. It is done: new file lean/RestrictedTEUnitSphere.lean (see the end of this note and reviews/restricted_te_unit_sphere.md). It is an enabling wrapper for (iii), not one of (i) to (iv) themselves.

## (i) Finite physical background lift

What exists (explicit parity-device chain, fixed finite input):
- `OQ14.SmallParityInclusions.finite_small_balls_inverse`: for fixed centers, radius factor and positive gain factor b, there is delta>0 such that for all 0<a<delta and every coefficient bounded by C and supported in the balls, the explicit block `weightedBlock c - perturbation d k (b/a)` is a unit with `‖Ring.inverse ...‖ ≤ 2`.
- `OQ14.ParityMaterialField.block_eq`: `block d k B = DynamicVolume.volumeBlock c k d.radius - ((B^2-1:ℝ):ℂ) • ParityReactionVolume.operator d true k - ((B⁻¹^2-1:ℝ):ℂ) • ParityReactionVolume.operator d false k`. The module header states explicitly that this "is not an identification with a finite radial-background Green field".
- `OQ14.ParityCompleteLimit.total_to_trial` and `OQ14.FiniteSphereDipoleLimit.actual_inverse_limit` (Herglotz incident) and `OQ14.RestrictedTEDipoleLimit.actual_inverse_to_dipoles` (finite harmonic TE incident, whole-plane L1 limit of `RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a:ℂ)⁻¹ • A)` to `RestrictedTEDipoleError.dipoleFlux ...`), plus `RestrictedTETotalLimit.actual_inverse_to_static`, `RestrictedTEFreeLimit.actual_inverse_to_static`.
- Uniform finite-input versions: `RestrictedTETotalLinear.uniform_actual_inverse_to_dipoles` (sup-norm polydisc on a finite index set) and now `RestrictedTEUnitSphere.uniform_unit_sphere` and `uniform_physical_unit_ball`.
- Physical radial stack (the other side of the bridge), all for fixed degree/finite jets: `OQ14.RadialPhaseLimit.actual_gamma_limit (l) (gs : List Segment) : Tendsto (fun n => RadialSource.gamma l (layers gs (radius n) (radius_pos n)) (radius n) (radius n+width gs) (radius_pos n)) atTop (𝓝 ((limitingCoefficients l gs).1/(limitingCoefficients l gs).2))`; `OQ14.RadialParityLimit.actual_gamma_even_limit` (limit -I*(q/sigma)^(2n)) and `actual_gamma_odd_limit`; `OQ14.RadialFiniteLimit.finite_stack_limit`; and `OQ14.PhysicalReactionLimit.uniform_physical_jet_limit (gs) (q M b B) (j) (hq : 1<=q) (hM) (hb) (hB : 1<=B) (hbB : degreeScale j b<=B) (hp : ∀ g∈gs, 1<=g.σ ∧ g.σ<=M ∧ g.q^2<=M ∧ g.q<=q) : Tendsto (fun n => ∑' a : TotalIndex, actualMap gs j b n a) atTop (𝓝 (∑' a : TotalIndex, limitMap gs j b a))`. Its own review says this is "not yet the full layered Green/dyadic identification".
- Local geometry for the shell bridge: ShellInclusionCells (`cell`, `cells_reachable`, `partition`), and root's ShellInclusionAlgebra / ShellInclusionBlocks / ShellInclusionVolume (`volumeBlock_eq_sandwich : DynamicVolume.volumeBlock c k R = 1 - sqrtMultiplier c * kernel k R * sqrtMultiplier c`, `combined_eq`, `effective_of_solution`, `combined_inverse`).

What is missing (smallest theorem): the identification of the actual finite-stack source Green kernel with the explicit parity kernel, i.e. that the kernel entering `ParityMaterialField.block` is the limit of the genuine layered Green kernel. Proposed shape (types of the Green object to be fixed with root and the modal track; not compiled):

    theorem physical_green_limit (gs : List Segment) (R : ℝ) (x y : Space) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (i j : Fin 3) :
      Tendsto (fun n : ℕ => actualGreen gs (radius n) x y i j) atTop
        (𝓝 (K0 k x y i j + ((B^2-1:ℝ):ℂ) * SphereReactionKernel.reaction true k x y i j
            + ((B⁻¹^2-1:ℝ):ℂ) * SphereReactionKernel.reaction false k x y i j))

uniformly for x,y in the ball, with `actualGreen` the dyadic source Green kernel of the stack, B the stack gain, and the same statement for the paired magnetic kernel, plus inverse stability (the actual perturbed block with the stack Green kernel is a unit with the same bound for large n). Feasibility: very low in the near term; this is the major bridge owned by root and the modal track.

## (ii) Complete outgoing power and frequency (Poynting) normalization bridge

What exists:
- Incoming normalization: `RestrictedTEInput.input_norm_sq (A) : ‖input A‖^2 = physicalPower A` and `RestrictedTEPower.physical_power_pos`; `FiniteTEIncomingPower.actual_power_limit (s l p) (hp) (hh) (A) : Tendsto (spherePower s l p A) atTop (𝓝 (incomingPower s l p A))`; `RestrictedTEIncoming.physicalPower` with its sphere limit (RestrictedTEIncoming line 77).
- Outgoing far-field power: `FarFieldPower.actual_radial_power_limit (k R) (hR) (ρ) (hρ) (hc) (n) (hn) : Tendsto (fun r => r^2 * radialPower n (ExteriorContinuity.electric k ρ (r • n)) (MagneticResponse.magnetic k ρ (r • n))) atTop (𝓝 (energy (electricAmplitude k ρ n) / 2))`; `RadiatingFieldPower.flux_limit` (sphere flux of E,H with prescribed leading amplitude A tends to `∫ n, energy (A n)/2 ∂angularMeasure`), `far_energy_zero`, `electric_mass_zero`.
- Local conservation: `MaterialPower.testMaxwell_power (k ε hε M hb E H hE hH hMax χ hχ hcχ) : Integrable (powerPair χ E H) volume ∧ (∫ x, powerPair χ E H x) = 0` and `regional_power`; `HomogeneousVolumePower.homogeneous_spherical_power_limit_zero` (derived zero outgoing power for actual homogeneous fields); WeakPoynting; `SourceRadiationFrequency.te_outgoing_maxwell`, `tm_outgoing_maxwell` (actual outgoing source fields at arbitrary positive frequency).
- Channel algebra that consumes the normalization: OQ14.lean `isometry_perturbation_power_threshold`, `compression_power_threshold`, `absolute_bypass_certificate`, `quadratic_flux_norm_bound`.

What is missing (smallest theorems), in order:
(a) Constancy of the lossless sphere flux for the actual complete solution. Proposed: for real bounded measurable eps and a TestMaxwell pair with local L2 regularity, `∃ P : ℝ, ∀ᵐ r in Ioi R0, RadialFlux.flux E H r = P` (take radial cutoffs chi = phi(|x|) in `testMaxwell_power`, which gives ∫ phi'(r) F(r) dr = 0 for all test phi). The needed analysis is the passage from `testMaxwell_power` to a statement about spherical shell integrals (polar coordinates for the weak identity).
(b) Unit throughput: for the complete field E = E_inc + E_sc with regular incident of Herglotz amplitude `RestrictedTEAmplitude.amplitude A` and outgoing scattered far amplitude F, the limiting total outgoing energy equals the incoming energy, i.e. the scattering map is isometric on the actual input space: proposed `‖out(A)‖^2 = physicalPower A`, where out(A) is the antipodal-reflected incident amplitude plus F. This combines (a), `flux_limit` and `FiniteTEIncomingPower.actual_power_limit`, and needs the cross terms between incoming spherical amplitude and outgoing amplitude to vanish in the limit (they oscillate as e^(+-2ikr)); no such Riemann-Lebesgue step is in the tree yet.
(c) `ca:powerbudget` (hemisphere conservation, `eta*tau <= 1+delta`) has no Lean counterpart; it needs (a) and a hemisphere split of the flux, and only closes an empty regime.
Feasibility: (a) medium, (b) medium to hard, (c) medium after (a)/(b).

## (iii) Final counted-channel construction

What exists:
- Finite-dimensional rank/threshold algebra (OQ14.lean): `finite_rank_channel_bound`, `finite_rank_power_channel_bound (U R) (τ) (M) (hτ) (hpower : ∀ x, τ*‖x‖^2 ≤ ‖U x‖^2) (hgap : ‖U-R‖ < sqrt τ) ... : FiniteDimensional 𝕜 E ∧ finrank 𝕜 E ≤ M`, `isometry_perturbation_power_threshold`, `compression_power_threshold (T C U e τ hτ hC herror hmargin x hx) : τ*‖x‖^2 < ‖T x‖^2`, `absolute_bypass_certificate`.
- Orthonormal physical input construction: `PhysicalTEBandInterpolation.interpolate (r hr y hy p h0 h1 h2 n target) : ∃ scale>0, ∃ L, ∃ A : Fin n → (Index →₀ ℂ), (∀ j q, q ∈ (A j).support → Even q.val.1 ∧ 2 ≤ q.val.1 ∧ q.val.1 ≤ L) ∧ (∀ j, fieldJet p (A j) = (1/(sqrt scale:ℂ)) • target j) ∧ Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))`; `PhysicalGramNormalization.interpolate`, `PhysicalGramBalance.balance`, `HermitianGramCompletion.completion (G) (hG : G.IsHermitian) : ∃ scale>0, ∃ B, Bᴴ*B = scale • 1 - G`.
- Uniform whole-plane flux convergence on the unit ball of that orthonormal space: `RestrictedTEUnitSphere.uniform_physical_unit_ball` (new), built on `RestrictedTETotalLinear.uniform_actual_inverse_to_dipoles`.
- Manuscript-only: ct:model (coherent diagonal passage/bypass model), uc:counterexample (diagonal choice of a and radius).

What is missing (smallest theorems), in order:
(a) Abstract transfer of a uniform L1 flux error to passage/bypass thresholds. Proposed (not compiled):

    theorem passage_bypass_transfer {V : Type*} (n2 : V → ℝ) (D : Set Plane) (hD : MeasurableSet D)
        (f g : V → Plane → ℂ) (hf : ∀ x, Integrable (f x)) (hg : ∀ x, Integrable (g x)) (p0 p1 ε : ℝ)
        (herr : ∀ x, ∫ q, ‖f x q - g x q‖ ≤ ε * n2 x)
        (hpass : ∀ x, p0 * n2 x ≤ (∫ q in D, g x q).re) (hbyp : ∀ x, ∫ q in Dᶜ, ‖g x q‖ ≤ p1 * n2 x) :
        ∀ x, (p0-ε) * n2 x ≤ (∫ q in D, f x q).re ∧ ∫ q in Dᶜ, ‖f x q‖ ≤ (p1+ε) * n2 x

Elementary; the work is only in connecting it to `diffForm`/`uniform_physical_unit_ball`.
(b) The model hypotheses `hpass`/`hbyp` for the exact dipole flux `dipForm` of the Gram-balanced jets: section integral over D of the exact dipole flux tends to the jet Gram value as a -> 0 and the outside-D integral tends to zero. This needs the plane integral/concentration of the normal dipole field (existing support: `StaticPlaneKernel.envelope_integral`, `translated_envelope_integral`, `StaticBallPlaneDipole.plane_response_eq_dipole`, `StaticPlaneDipoleError.moving_gap_mass`) and the jet replacement p a l -> p_j (background Lipschitz O(1/a) after the 1/a scaling): proposed statement `Tendsto (fun a => ∫ q, ‖dipoleFlux (p a) ... A' q - jetDipoleFlux p_j ... A' q‖) (𝓝[>] 0) (𝓝 0)` uniformly on the physical unit ball, then the explicit section integral of `jetDipoleFlux`.
(c) Choice of p0 strictly between eta and delta and the finite stages (gain, then radius, diagonal sequence), and the combination with (ii) unit throughput and (i). Without (i) and (ii) this cannot be stated about the actual physical device.
Feasibility: (a) high, (b) medium to hard (long analytic estimate, but all ingredients are in the tree), (c) blocked on (i),(ii).

## (iv) Named even-m vector harmonic basis identification

What exists:
- Intrinsic even sector, not m-labelled: `HarmonicHalfTurn.project`, `project_homogeneous`, `project_harmonic`, `project_invariant (p x) : evaluate (project p) (rotation x) = evaluate (project p) x` (rotation by pi about z); `EvenHarmonicProjection.project l p := if Even l then HarmonicHalfTurn.project p else 0` with `homogeneous`, `harmonic`, `invariant`, `central_even`, `equator_even`; `RestrictedTEIncoming.polynomial q := EvenHarmonicProjection.project q.val.1 q.val.2`; `RestrictedTEEffectiveBand.Active q := Even q.val.1 ∧ 2 ≤ q.val.1`, `column_zero`, `effective`, `input_eq`, `jets_eq`; `PhysicalTEBandInterpolation.interpolate` (support in Active and degree <= L).
- Abstract bases: `SphereHarmonicBasis.basis l : OrthonormalBasis (Index l) ℝ (harmonicSpace l)` (indexed by `Fin (finrank ...)`, no m label), `angular_orthonormal`, `angularSpan_dense`; `SphereHarmonicDimension.harmonicSpace_finrank_le` (an upper bound only); `VectorHarmonicBasisSpan.basisSpan_dense`; `TransverseHarmonicBasis.hilbertBasis : HilbertBasis (PositiveIndex ⊕ PositiveIndex) ℝ transverseSpace`, `expansion`, `parseval`. HankelRealBasis is the radial Hankel/real vacuum basis, not an angular basis.
- Caution on the coefficient space: `SymmetricHarmonicJets.Index` is the subtype of ALL pairs (l, p) with p homogeneous harmonic of degree l, so `Index →₀ ℂ` is a free space on polynomials, not a basis coordinate space. The faithful finite physical space is `RestrictedTEInputJets.IncomingSpace := LinearMap.range RestrictedTEInput.input` (norm = physical power by `input_norm_sq`).

What is missing: (1) an m-labelled real/complex basis (Y_l^m or equivalent polynomials) with the half-turn acting by (-1)^m; (2) exact dimension of the invariant harmonic space ((l+1) for even l); (3) the statement that `range input` restricted to degrees l <= L equals the span of the even-m TE fields. Smallest proposed theorem (not compiled): for each even l >= 2, `finrank ℂ (Submodule.span ℂ {RestrictedTEInput.input (Finsupp.single q 1) | q.val.1 = l}) = l+1`. Note that the manuscript's ct:jets existence statement (even l >= 2, even m) is already delivered in intrinsic form by `PhysicalTEBandInterpolation.interpolate`; the m-labelled identification is bookkeeping to retain the manuscript's label, not a mathematical gap for the channel count. The existing Lean interpolation also requires the special geometry p_j = (r, y_j, 0), y_j distinct, which implies p_i != +-p_j but is narrower than the manuscript's arbitrary nonzero plane points.
Feasibility: low to medium (needs explicit harmonic polynomials/dimension count, none of which is in Mathlib in usable form).

## (v) Coordination with root's shell/inclusion/remote-annulus bridge

State: ShellInclusionVolume gives `volumeBlock_eq_sandwich` and the exact shell/combined/effective/inverse blocks for `DynamicVolume.volumeBlock` of a disjoint shell-plus-inclusion coefficient, with `kernel k R := DynamicConvolution.operator k (2*R) - VectorFourier.physicalProjection`.
Pending kernel identification (as root states): the parity device uses `ParityMaterialField.block d k B = volumeBlock c k d.radius - (B^2-1)•ParityReactionVolume.operator d true k - (B⁻¹^2-1)•ParityReactionVolume.operator d false k` (`block_eq`). To apply the same block algebra one needs a bounded kernel operator `T_B` on `VectorL2` with `ParityMaterialField.block d k B = 1 - sqrtMultiplier c * T_B * sqrtMultiplier c`. A bounded T_B must be chosen as the compression to the support ball (the entire reaction kernel is unbounded on all of L2). Proposed (not compiled): define `reactionBall d e k : Operator := chi_R * (operator on the ball) * chi_R` and prove `ParityReactionVolume.operator d e k = sqrtMultiplier c * reactionBall d e k * sqrtMultiplier c` using `BoundedMaterialKernel.operator`'s definition and the fact that `sqrtMultiplier c` vanishes off the carrier. Feasibility: medium; it is a definitional unfolding plus the a.e. support argument already used in `ShellInclusionVolume.sqrtMultiplier_add`. Coordinate with root before starting, since the combined shell+inclusion statement for the parity block should land in the same module as `combined_eq`.
Independent of this, remote-annulus whole-plane L1 passage and (i) remain with root/modal.

## Feasibility ranking (most to least)

1. Done: physical-power unit ball wrapper (`RestrictedTEUnitSphere`).
2. (iii)(a) passage/bypass transfer lemma: elementary integral algebra.
3. (v) parity block sandwich identification: unfolding plus support argument.
4. (ii)(a) lossless sphere-flux constancy from `testMaxwell_power`: needs polar-coordinate weak formulation.
5. (iii)(b) concentration of exact dipole flux and jet replacement: long but all inputs present.
6. (ii)(b),(c) unit throughput, power budget: needs a Riemann-Lebesgue cross-term step not in the tree.
7. (iv) m-labelled basis: explicit harmonic polynomials and exact dimensions absent from Mathlib.
8. (i) physical finite-stack Green identification: the major open bridge (root/modal).

## New proved item attached to this note: `RestrictedTEUnitSphere`

lean/RestrictedTEUnitSphere.lean (imports RestrictedTETotalLinear, RestrictedTEInput). Theorems (`#print axioms` standard-only each): `diffForm_scale`, `unit_sphere_form`, `uniform_unit_sphere`, `uniform_physical_unit_ball`. Statement of the last (hypotheses as in `actual_inverse_to_dipoles`):

    ∀ᶠ a in 𝓝[>] 0, ∀ A' : Index →₀ ℂ, A' ∈ Submodule.span ℂ (Set.range A) → physicalPower A' ≤ 1 →
      Integrable (fun q => totalFlux (b/a) (source p ρ χ R b hρ hχ hi A' a) ((a:ℂ)⁻¹ • A') q - dipoleFlux (p a) (fun _ => ρ*a) (fun l => polarization χ (electric ((a:ℂ)⁻¹ • A') (p a l))) ((a:ℂ)⁻¹ • A') q)
      ∧ (∫ q, ‖... same ...‖) ≤ ε

for a finite family `A : κ → Index →₀ ℂ` with `Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))`. This is the form needed by the section wrapper: the constructed interpolants of `PhysicalTEBandInterpolation.interpolate` satisfy the hypothesis on A. Not proved there: the replacement of the ball-center values by the plane jets and the explicit section integrals (iii)(b).

import RestrictedTEActualWindow
import SourcePairedSolutionFormula

/-! The counted-subspace theorem of the actual device through one fixed square, within a fixed permittivity
interval.

Fixed square.  The dipole points lie on the line `x = -L`, the left edge of the square
`Dsq L = {|x| < L, |y| < L}`, at the heights `y_l = (l+1)/(N+1) L ∈ (0, L)` of a fixed segment, and the existing
normal `nvec = (1, 0)` points into the square.  Their half-turn images lie on the right edge, where the inward
normal is `-nvec`; the square is symmetric under `q ↦ -q`.  The interpolation theorem and the concrete counting
proof are valid for every nonzero `r`, so the proof of `RestrictedTEActualWindow.doubled_counting_of_interp` is
repeated with `r ≠ 0` instead of `r > 0`; the passage constant and the window are unchanged.

Permittivity.  The coefficient of the paired shell has values in `[0, q² - 1]`, the inclusion values lie in
`[0, χ]`, the supports are disjoint, hence `1 ≤ ε ≤ max (q², 1 + χ)`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualSquare
open MeasureTheory Filter Topology OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting
  OQ14.RestrictedTEActualWindow OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration
  OQ14.RestrictedTEConcreteDevice OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls
  OQ14.RestrictedTEPlaneJets OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness
  OQ14.ChannelMaterialThroughput SymmetricHarmonicJets RestrictedTEPlaneLocal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The square section -/

/-- The open square of half-side `L` centred at the origin. -/
def Dsq (L : ℝ) : Set PlaneInverseCube.Plane := {q | |q 0| < L ∧ |q 1| < L}

theorem Dsq_neg (L : ℝ) (q : PlaneInverseCube.Plane) : -q ∈ Dsq L ↔ q ∈ Dsq L := by
  simp [Dsq, abs_neg]

theorem Dsq_measurable (L : ℝ) : MeasurableSet (Dsq L) := by
  have h0 : Measurable (fun q : PlaneInverseCube.Plane => |q 0|) :=
    (continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).measurable
  have h1 : Measurable (fun q : PlaneInverseCube.Plane => |q 1|) :=
    (continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).measurable
  exact (measurableSet_lt h0 measurable_const).inter (measurableSet_lt h1 measurable_const)

theorem Dsq_bounded (L : ℝ) : Bornology.IsBounded (Dsq L) := by
  refine (Metric.isBounded_ball (x := (0 : PlaneInverseCube.Plane)) (r := 2 * L)).subset ?_
  intro q hq
  obtain ⟨h0, h1⟩ := hq
  have hL : 0 < L := lt_of_le_of_lt (abs_nonneg _) h0
  rw [Metric.mem_ball, dist_zero_right]
  refine (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp ?_
  rw [norm_sq_plane]
  have a0 : (q 0) ^ 2 < L ^ 2 := sq_lt_sq' (abs_lt.mp h0).1 (abs_lt.mp h0).2
  have a1 : (q 1) ^ 2 < L ^ 2 := sq_lt_sq' (abs_lt.mp h1).1 (abs_lt.mp h1).2
  nlinarith

/-- The square has the local half-plane structure at the points `(-L, y_l)` of its left edge with the inward
normal `nvec = (1, 0)`, provided `0 < y_l < L`. -/
theorem Dsq_local (L : ℝ) (y : ι → ℝ) (hy : ∀ l, 0 < y l ∧ y l < L) (l : ι) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      Dsq L ∩ Metric.closedBall (hpoint (-L) y l) s =
        (fun q => q - hpoint (-L) y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s) := by
  refine ⟨(L - y l) / 2, by linarith [(hy l).2], ?_⟩
  intro s hs hs0
  ext q
  have hn0 := PiLp.norm_apply_le (q - hpoint (-L) y l) 0
  have hn1 := PiLp.norm_apply_le (q - hpoint (-L) y l) 1
  rw [Real.norm_eq_abs] at hn0 hn1
  simp only [Dsq, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, U, Metric.mem_closedBall,
    dist_zero_right, sub_zero, dist_eq_norm, ip_apply, nvec_zero, nvec_one, PiLp.sub_apply, hpoint_zero,
    hpoint_one] at hn0 hn1 ⊢
  have hyl := hy l
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    have h3 : |q 0 - -L| ≤ s := hn0.trans h2
    have h4 := abs_lt.mp h1
    exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    have h3 : |q 0 - -L| ≤ s := hn0.trans h2
    have h5 : |q 1 - y l| ≤ s := hn1.trans h2
    have h3' := abs_le.mp h3
    have h5' := abs_le.mp h5
    refine ⟨⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩, h2⟩

/-! ### Geometry on a fixed segment -/

/-- `N` points `y_l = (l+1)/(N+1) L` on the segment `(0, L)`. -/
def ysq (N : ℕ) (L : ℝ) : Fin N → ℝ := fun l => (((l : ℕ) : ℝ) + 1) / ((N : ℝ) + 1) * L

theorem ysq_pos_lt (N : ℕ) (L : ℝ) (hL : 0 < L) (l : Fin N) : 0 < ysq N L l ∧ ysq N L l < L := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hl : ((l : ℕ) : ℝ) + 1 < (N : ℝ) + 1 := by
    have : ((l : ℕ) : ℝ) < N := by exact_mod_cast l.is_lt
    linarith
  constructor
  · unfold ysq
    positivity
  · unfold ysq
    have : (((l : ℕ) : ℝ) + 1) / ((N : ℝ) + 1) < 1 := (div_lt_one hN).mpr hl
    nlinarith

theorem ysq_diff (N : ℕ) (L : ℝ) (i j : Fin N) :
    ysq N L i - ysq N L j = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * (L / ((N : ℝ) + 1)) := by
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold ysq
  field_simp
  ring

theorem ysq_injective (N : ℕ) (L : ℝ) (hL : 0 < L) : Function.Injective (ysq N L) := by
  intro i j hij
  have h := ysq_diff N L i j
  rw [hij, sub_self] at h
  have hc : 0 < L / ((N : ℝ) + 1) := by positivity
  have h2 : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h.symm with h3 | h3
    · exact h3
    · exact absurd h3 hc.ne'
  exact Fin.ext (by exact_mod_cast sub_eq_zero.mp h2)

theorem ysq_sep (N : ℕ) (L h a : ℝ) (hL : 0 < L) (i j : Fin N) (hij : i ≠ j) :
    L / ((N : ℝ) + 1) ≤ dist (abovePoint (hpoint (-L) (ysq N L) i) (h * a))
      (abovePoint (hpoint (-L) (ysq N L) j) (h * a)) := by
  rw [dist_eq_norm]
  have hn := PiLp.norm_apply_le (abovePoint (hpoint (-L) (ysq N L) i) (h * a) -
    abovePoint (hpoint (-L) (ysq N L) j) (h * a)) 1
  rw [PiLp.sub_apply, abovePoint_coord_one, abovePoint_coord_one, hpoint_one, hpoint_one, Real.norm_eq_abs] at hn
  refine le_trans ?_ hn
  rw [ysq_diff, abs_mul]
  have hc : 0 < L / ((N : ℝ) + 1) := by positivity
  rw [abs_of_pos hc]
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
  have h1 : 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  nlinarith

theorem ysq_norm_le (N : ℕ) (L h a : ℝ) (hL : 0 < L) (hh : 0 ≤ h) (ha : 0 ≤ a) (ha1 : a ≤ 1) (l : Fin N) :
    ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ ≤ 2 * L + h := by
  have hy := ysq_pos_lt N L hL l
  have hha : h * a ≤ h := mul_le_of_le_one_right hh ha1
  have hha0 : 0 ≤ h * a := mul_nonneg hh ha
  have hb : 0 ≤ 2 * L + h := by linarith
  refine (sq_le_sq₀ (norm_nonneg _) hb).mp ?_
  rw [abovePoint_norm_sq, hpoint_zero, hpoint_one]
  nlinarith [hy.1, hy.2]

/-- Geometry of the device on the fixed square for every `N`. -/
theorem device_geometry_square (N : ℕ) (L h ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hρh : ρ < h) :
    Function.Injective (ysq N L) ∧ (∀ l, 0 < ysq N L l ∧ ysq N L l < L) ∧
    (∀ a, 0 < a → a ≤ 1 → ∀ i j : Fin N, i ≠ j →
      L / ((N : ℝ) + 1) ≤ dist (abovePoint (hpoint (-L) (ysq N L) i) (h * a))
        (abovePoint (hpoint (-L) (ysq N L) j) (h * a))) ∧
    (∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
      ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ 2 * L + 2 * h) := by
  refine ⟨ysq_injective N L hL, ysq_pos_lt N L hL, fun a _ _ i j hij => ysq_sep N L h a hL i j hij, ?_⟩
  intro a ha ha1 l
  have hh : 0 ≤ h := by linarith
  have := ysq_norm_le N L h a hL hh ha.le ha1 l
  linarith

/-! ### Counting for the device on the line `x = r`, `r ≠ 0` -/

/-- The second stage of the concrete doubled counting theorem for any nonzero line position `r`: the proof of
`RestrictedTEActualWindow.doubled_counting_of_interp` with `r ≠ 0` instead of `r > 0`. -/
theorem doubled_counting_of_interp_ne (r : ℝ) (hr : r ≠ 0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R) (hb : b ≠ 0)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r y i) (h * a)) (abovePoint (hpoint r y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r y l) (h * a)‖ + ρ ≤ R)
    (D : Set PlaneInverseCube.Plane) (hDsym : ∀ q : PlaneInverseCube.Plane, -q ∈ D ↔ q ∈ D)
    (hDloc : ∀ l, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      D ∩ Metric.closedBall (hpoint r y l) s = (fun q => q - hpoint r y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s))
    (scale : ℝ) (hs : 0 < scale) (A : Fin (Fintype.card ι) → Index →₀ ℂ)
    (hjet : ∀ j, RestrictedTEJetMap.fieldJet (pts r y) (A j) =
      (1 / (Real.sqrt scale : ℂ)) • target χ (Fintype.equivFin ι) j)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) :
    ∀ ηt δt : ℝ, ηt < 2 * (Vb ρ * halfPlane nvec h / scale) → 2 * (Vb ρ * halfPlane nvec h / scale) < δt →
      ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A' ∈ Submodule.span ℂ (Set.range A),
        RestrictedTEIncoming.physicalPower A' = 1 →
        ηt ≤ passage volume D
            (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h * a))) ρ χ R b hρ hχ.le
              (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h * a)) ρ R hi) a A') ∧
        bypass volume D
            (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h * a))) ρ χ R b hρ hχ.le
              (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h * a)) ρ R hi) a A') ≤ δt := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  intro ηt δt hlo hhi
  have hhpos : ∀ _ : ι, 0 < h := fun _ => by linarith
  have hγ : 0 < h - ρ := by linarith
  have hh1 : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ l : ι, ((h - ρ) + ρ) * a ≤
      |(abovePoint (hpoint r y l) (h * a)) 2| := by
    intro a ha _ l
    rw [above_normal, abs_of_pos (mul_pos (by linarith) ha)]
    linarith
  have hspan : ∀ A' ∈ Submodule.span ℂ (Set.range A), ∃ cf : Fin (Fintype.card ι) → ℂ, ∑ k, cf k • A k = A' :=
    fun A' hA' => (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA'
  have hT : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 → ∀ l,
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 0 =
        -(mj A' (hpoint r y) (fun _ => nvec) l) * ((nvec 1 : ℝ) : ℂ) ∧
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 1 =
        mj A' (hpoint r y) (fun _ => nvec) l * ((nvec 0 : ℝ) : ℂ) := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    obtain ⟨_, h2', h3'⟩ := jets_of_interp r y scale χ e A hjet cf l
    unfold mj
    rw [h2', h3']
    simp [nvec_zero, nvec_one]
  have hK : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 → ∀ l,
      0 ≤ (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re ∧
        (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).im = 0 := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    rw [kap_value r y ρ scale χ hs hχ e A hjet cf l, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have : 0 ≤ Vb ρ := by unfold Vb; positivity
    positivity
  have hB : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 →
      ∑ l, (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re * halfPlane nvec h =
        Vb ρ * halfPlane nvec h / scale := by
    intro A' hA' hpow
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    have hsum : (∑ k, ‖cf k‖ ^ 2) = 1 := by rw [← power_comb A horth cf]; exact hpow
    simp_rw [kap_value r y ρ scale χ hs hχ e A hjet cf, Complex.ofReal_re]
    have : (∑ l : ι, Vb ρ * ‖cf (e l)‖ ^ 2 / scale * halfPlane nvec h) =
        Vb ρ * halfPlane nvec h / scale * ∑ l : ι, ‖cf (e l)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [this, Equiv.sum_comp e (fun k => ‖cf k‖ ^ 2), hsum, mul_one]
  have hsepD : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ i j : ι ⊕ ι, i ≠ j → min δ (2 * |r|) ≤
      dist (partnerCentre (fun l => abovePoint (hpoint r y l) (h * a)) i)
        (partnerCentre (fun l => abovePoint (hpoint r y l) (h * a)) j) :=
    fun a _ _ => partner_separation r δ (h * a) (hpoint r y) (fun l => hpoint_zero r y l) (hsep a ‹_› ‹_›)
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hδ' : 0 < min δ (2 * |r|) := lt_min hδ (by linarith)
  have hcdD : ∀ i j : ι ⊕ ι, i ≠ j → cD (hpoint r y) i ≠ cD (hpoint r y) j := by
    intro i j hij heq
    simp only [cD] at heq
    rcases i with l | l <;> rcases j with k | k
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) heq
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      exact hr (by linarith)
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      exact hr (by linarith)
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) (neg_inj.mp heq)
  exact doubled_device_counting (fun a l => abovePoint (hpoint r y l) (h * a)) ρ χ (min δ (2 * |r|)) R b (h - ρ)
    hρ hχ.le hδ' hR hb hγ hsepD (partner_hi_aux _ ρ R hi) (partner_hh_aux _ (h - ρ) ρ hh1)
    (hpoint r y) (fun _ => h) hhpos (fun a l => rfl) hcdD (fun _ => nvec) (fun _ => norm_nvec) D
    hDsym hDloc A horth hT hK (Vb ρ * halfPlane nvec h / scale) ηt δt hB hlo hhi

/-- Counted channels of the actual device for given interpolation data and a line position `r0 ≠ 0`. -/
theorem actual_counted_of_interp_ne (r0 : ℝ) (hr0 : r0 ≠ 0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r0 y i) (h * a)) (abovePoint (hpoint r0 y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (D : Set PlaneInverseCube.Plane) (hDsym : ∀ q : PlaneInverseCube.Plane, -q ∈ D ↔ q ∈ D)
    (hDloc : ∀ l, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      D ∩ Metric.closedBall (hpoint r0 y l) s = (fun q => q - hpoint r0 y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s))
    (q : ℝ) (hq : 1 < q) (jetScale : ℝ) (hs : 0 < jetScale) (A : Fin (Fintype.card ι) → Index →₀ ℂ)
    (hjet : ∀ j, RestrictedTEJetMap.fieldJet (pts r0 y) (A j) =
      (1 / (Real.sqrt jetScale : ℂ)) • target χ (Fintype.equivFin ι) j)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (Fact : ℕ → ℕ → (SymmetricHarmonicJets.Index →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hhom : HomogeneousFlux Fact) (H2 : L1Interface r0 y ρ χ h R hρ hχ hi q Fact)
    (ηt δt : ℝ) (hlo : ηt < 2 * (Vb ρ * halfPlane nvec h / jetScale))
    (hhi : 2 * (Vb ρ * halfPlane nvec h / jetScale) < δt) (τ : ℝ) (hτ : τ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
          (le_max_left R 1) hi q hq n r)
        (fun a => passage volume D (Fact n r a)) (fun a => bypass volume D (Fact n r a)) τ ηt δt := by
  have hb : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hcount := doubled_counting_of_interp_ne r0 hr0 y hy ρ χ h δ R 1 hρ hχ hh hδ hR one_ne_zero hsep hi D hDsym
    hDloc jetScale hs A hjet horth
  have H1 := hcount ((ηt + 2 * (Vb ρ * halfPlane nvec h / jetScale)) / 2)
    ((2 * (Vb ρ * halfPlane nvec h / jetScale) + δt) / 2) (by linarith) (by linarith)
  exact counted_of_counting volume D A horth (parityFlux r0 y ρ χ h R hρ hχ hi) Fact hhom
    (fun n => scale q n) (scale_tendsto_nhdsGT hq) ηt δt ((ηt + 2 * (Vb ρ * halfPlane nvec h / jetScale)) / 2)
    ((2 * (Vb ρ * halfPlane nvec h / jetScale) + δt) / 2) (by linarith) (by linarith) H1 (H2 _ A horth)
    (fun n r => actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
      (le_max_left R 1) hi q hq n r)
    ((actualScatter_norm_eventually (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
      hb (le_max_left R 1) hi q hq).mono (fun n hn => hn.mono (fun r hr x _ => hr x))) τ hτ

/-! ### Permittivity bounds of the paired device -/

theorem pairedCoeff_dielectric_bounds (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : FourierL2.Space, x ∉ Metric.closedBall (0 : FourierL2.Space) b → ci.value (VectorFourier.coordinateMap x) = 0)
    (εp : ℝ) (hq2 : q ^ 2 ≤ εp) (hc : ∀ ξ, ci.value ξ ≤ εp - 1) (x : FourierL2.Space) :
    1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq n r ci) x ∧
      MaterialMaxwell.dielectric (pairedCoeff q hq n r ci) x ≤ εp := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb hci (VectorFourier.coordinateMap x)
  have h1 := (SourcePairedInclusion.shell q hq n r).nonnegative (VectorFourier.coordinateMap x)
  have h2 := ci.nonnegative (VectorFourier.coordinateMap x)
  have h3 : (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap x) ≤ q ^ 2 - 1 :=
    (SourcePairedInclusion.shell q hq n r).bounded (VectorFourier.coordinateMap x)
  have h4 := hc (VectorFourier.coordinateMap x)
  have hv : (pairedCoeff q hq n r ci).value (VectorFourier.coordinateMap x) =
      (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap x) +
        ci.value (VectorFourier.coordinateMap x) := rfl
  unfold MaterialMaxwell.dielectric
  rw [hv]
  constructor
  · linarith
  · rcases hd with h5 | h5
    · rw [h5]; linarith
    · rw [h5]; linarith

theorem device_coeff_vanish (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) (n : ℕ) :
    ∀ x : FourierL2.Space, x ∉ Metric.closedBall (0 : FourierL2.Space) b → (deviceCoeff p ρ χ hχ q n).value
      (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  have hin : ∀ l, ‖p (scale q n) l‖ + ρ * scale q n ≤ R := fun l =>
    (add_le_add_left (mul_le_of_le_one_right hρ.le (scale_le_one hq.le n)) _).trans
      (hi (scale q n) (scale_pos hq n) (scale_le_one hq.le n) l)
  exact partner_zero_outside (p (scale q n)) (fun _ : ι => ρ * scale q n) χ hχ R hin x
    (fun h => hx (Metric.closedBall_subset_closedBall hRb h))

/-- Permittivity bounds of the actual paired device: whenever `q² ≤ ε₊`, `1 + χ ≤ ε₊` and the inclusion radius lies
inside the inner shell radius, the dielectric function of the combined coefficient takes values in `[1, ε₊]`. -/
theorem device_permittivity_bounds (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hRb : R ≤ b) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) (n r : ℕ)
    (hbR : b ≤ (SourcePairedInclusion.data q hq.le n r).R) (εp : ℝ) (hq2 : q ^ 2 ≤ εp) (hχε : 1 + χ ≤ εp)
    (x : FourierL2.Space) :
    1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r (deviceCoeff p ρ χ hχ q n)) x ∧
      MaterialMaxwell.dielectric (pairedCoeff q hq.le n r (deviceCoeff p ρ χ hχ q n)) x ≤ εp :=
  pairedCoeff_dielectric_bounds q hq.le n r (deviceCoeff p ρ χ hχ q n) b hbR
    (device_coeff_vanish p ρ χ R b hρ hχ hRb hi q hq n) εp hq2
    (fun ξ => ((deviceCoeff p ρ χ hχ q n).bounded ξ).trans (by
      change χ ≤ εp - 1
      linarith)) x

/-! ### The final statement -/

/-- The counted-subspace theorem of the actual device through one fixed square, within a fixed permittivity
interval.  For every `ε₊ > 1`, every half-side `L > 0` of the fixed square `Dsq L`, every `N`, every thresholds
`0 < η < δ` and every `τ ≤ 1` there are a shell ratio `q` with `1 < q² ≤ ε₊`, a contrast `χ` with `1 + χ ≤ ε₊`,
an explicit doubled device (points `(-L, y_l)`, `y_l = (l+1)/(N+1) L`, half-turn images on the right edge) and an
orthonormal family of `N` finite inputs such that the dielectric of the actual paired-shell device takes values in
`[1, ε₊]` (eventually in the shell index `r`, for every gain index `n`), and, for every plane flux family `Fact` of the
actual device that is homogeneous and satisfies the whole-plane L1 interface, the span of the inputs is a counted
subspace through the square, eventually in `n` and then in `r`. -/
theorem actual_counted_subspaces_square (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (_ : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∃ _ : max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R,
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ∧
          MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ≤ εp) ∧
      ∀ Fact : ℕ → ℕ → (SymmetricHarmonicJets.Index →₀ ℂ) → PlaneInverseCube.Plane → ℂ, HomogeneousFlux Fact →
        L1Interface (-L) (ysq N L) ρ χ h R hρ hχ hi q Fact →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (Fact n r a))
            (fun a => bypass volume (Dsq L) (Fact n r a)) τ η δ := by
  -- the permittivity data
  have hmid : 1 < (1 + εp) / 2 := by linarith
  set q : ℝ := Real.sqrt ((1 + εp) / 2) with hqdef
  have hq : 1 < q := by
    rw [hqdef]
    exact Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hq2 : q ^ 2 ≤ εp := by
    rw [hqdef, Real.sq_sqrt (by linarith)]
    linarith
  set χ : ℝ := min 1 (εp - 1) with hχdef
  have hχ : 0 < χ := lt_min one_pos (by linarith)
  have hχε : 1 + χ ≤ εp := by
    have := min_le_right 1 (εp - 1)
    linarith
  -- the interpolation family, chosen first: it depends only on `-L`, `y`, `χ`
  let y : Fin N → ℝ := ysq N L
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) := Fintype.equivFin (Fin N)
  have hy : Function.Injective y := ysq_injective N L hL
  have hr0' : (-L) ≠ 0 := by linarith
  have h0 : ∀ l, pts (-L) y l 0 = -L := fun l => by simp [pts, abovePoint, hpoint]
  have h1 : ∀ l, pts (-L) y l 1 = y l := fun l => by simp [pts, abovePoint, hpoint]
  have h2 : ∀ l, pts (-L) y l 2 = 0 := fun l => by simp [pts, abovePoint]
  obtain ⟨jetScale, hs, Lj, A0, _, hjet, horth0⟩ := PhysicalTEBandInterpolation.interpolate (-L) hr0' y hy
    (pts (-L) y) h0 h1 h2 (Fintype.card (Fin N)) (target χ e)
  -- the window, chosen after the jet scale
  obtain ⟨h, ρ, hρ, hρh, hlo, hhi⟩ := window_choice η δ jetScale hη hηδ hs
  have hgeo := device_geometry_square N L h ρ hL hρ hρh
  have hh0 : 0 < h := lt_trans hρ hρh
  set R : ℝ := 2 * L + 2 * h with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; linarith
  have hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N, ‖abovePoint (hpoint (-L) y l) (h * a)‖ + ρ ≤ R := hgeo.2.2.2
  have hsep := hgeo.2.2.1
  have hδsep : 0 < L / ((N : ℝ) + 1) := by positivity
  -- the transported family indexed by `Fin N`
  let e0 : Fin N ≃ Fin (Fintype.card (Fin N)) := finCongr (Fintype.card_fin N).symm
  have hrange : Set.range (A0 ∘ e0) = Set.range A0 := e0.surjective.range_comp A0
  have hli : LinearIndependent ℂ A0 :=
    LinearIndependent.of_comp (RestrictedTEInput.input : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] ComplexVectorSphere.Ambient)
      horth0.linearIndependent
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A0 ∘ e0, hq2, hχε, horth0.comp e0 e0.injective, ?_, ?_, ?_⟩
  · rw [hrange, finrank_span_eq_card hli]
    simp
  · intro n
    filter_upwards [SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1)] with r hbR
    exact ⟨hbR.le, fun x => device_permittivity_bounds (fun a l => abovePoint (hpoint (-L) y l) (h * a)) ρ χ R
      (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r hbR.le εp hq2 hχε x⟩
  · intro Fact hhom H2
    rw [hrange]
    exact actual_counted_of_interp_ne (-L) hr0' y hy ρ χ h (L / ((N : ℝ) + 1)) R hρ hχ hρh hδsep hR hsep hi
      (Dsq L) (Dsq_neg L) (Dsq_local L y hgeo.2.1) q hq jetScale hs A0 hjet horth0 Fact hhom H2 η δ hlo hhi τ hτ

end OQ14.RestrictedTEActualSquare
#print axioms OQ14.RestrictedTEActualSquare.Dsq_neg
#print axioms OQ14.RestrictedTEActualSquare.Dsq_measurable
#print axioms OQ14.RestrictedTEActualSquare.Dsq_bounded
#print axioms OQ14.RestrictedTEActualSquare.Dsq_local
#print axioms OQ14.RestrictedTEActualSquare.ysq_pos_lt
#print axioms OQ14.RestrictedTEActualSquare.ysq_diff
#print axioms OQ14.RestrictedTEActualSquare.ysq_injective
#print axioms OQ14.RestrictedTEActualSquare.ysq_sep
#print axioms OQ14.RestrictedTEActualSquare.ysq_norm_le
#print axioms OQ14.RestrictedTEActualSquare.device_geometry_square
#print axioms OQ14.RestrictedTEActualSquare.doubled_counting_of_interp_ne
#print axioms OQ14.RestrictedTEActualSquare.actual_counted_of_interp_ne
#print axioms OQ14.RestrictedTEActualSquare.pairedCoeff_dielectric_bounds
#print axioms OQ14.RestrictedTEActualSquare.device_coeff_vanish
#print axioms OQ14.RestrictedTEActualSquare.device_permittivity_bounds
#print axioms OQ14.RestrictedTEActualSquare.actual_counted_subspaces_square

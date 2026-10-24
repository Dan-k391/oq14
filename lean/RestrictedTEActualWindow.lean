import RestrictedTEActualCounting
import RestrictedTEHalfPlanePositive

/-! The counted-subspace theorem of the actual device in the manuscript's form `uc:counterexample`: for every
`N`, every fixed thresholds `0 < η < δ` and every `τ ≤ 1`, with the whole-plane L1 interface and the quadratic
homogeneity of the actual plane flux as the only hypotheses.

Window.  The interpolation family (`jetScale`, `A`) of `PhysicalTEBandInterpolation.interpolate` depends only on
the plane points `(r0, y_l, 0)` and on the contrast `χ` (the targets), not on the ball radius `ρ` nor on the height
`h`; so it is chosen first.  The passage constant of the doubled device is
`p0 = 2 Vb(ρ) halfPlane(nvec, h) / jetScale` and `halfPlane(nvec, h) = halfPlane(nvec, 1) / h`, hence
`p0(ρ = h/2) = (π/3) halfPlane(nvec, 1) h² / jetScale`, which takes the prescribed value `(η + δ)/2` for an
explicit `h`.  (The constraint `ρ < h` bounds `p0` above by `(2·4π/3) halfPlane(nvec,1) h² / jetScale` for a given
`h`, so the height `h` has to be chosen as well, after `jetScale`.)  Geometry.  The points `y_l = l` have
distances at least `1`, and `‖abovePoint‖ + ρ ≤ r0 + N + 2h`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualWindow
open MeasureTheory Filter Topology OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness
  SymmetricHarmonicJets RestrictedTEPlaneLocal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Scaling of the half-plane integral -/

theorem halfPlane_mul (n : PlaneInverseCube.Plane) (hn : ‖n‖ = 1) (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    a * halfPlane n (h * a) = halfPlane n h := by
  have h1 : Tendsto (fun s : ℝ => a * halfDisk n (h * a) s) atTop (𝓝 (a * halfPlane n (h * a))) :=
    (halfDisk_tendsto n hn (h * a) (mul_pos hh ha)).const_mul a
  have h2 : Tendsto (fun s : ℝ => a * halfDisk n (h * a) s) atTop (𝓝 (halfPlane n h)) := by
    have := (halfDisk_tendsto n hn h hh).comp (tendsto_id.atTop_div_const ha)
    refine this.congr (fun s => ?_)
    simp only [Function.comp_apply, id]
    exact (halfDisk_scale n h a s hh ha).symm
  exact tendsto_nhds_unique h1 h2

/-- `halfPlane n t = halfPlane n 1 / t`. -/
theorem halfPlane_inv (n : PlaneInverseCube.Plane) (hn : ‖n‖ = 1) (t : ℝ) (ht : 0 < t) :
    halfPlane n t = halfPlane n 1 / t := by
  have h := halfPlane_mul n hn 1 t one_pos ht
  rw [one_mul] at h
  field_simp
  linarith

/-! ### Window choice -/

/-- For prescribed thresholds `0 < η < δ` and any jet scale there are a height `h` and a ball ratio `ρ ∈ (0, h)`
with `η < p0 < δ`, where `p0 = 2 Vb(ρ) halfPlane(nvec, h) / jetScale`. -/
theorem window_choice (η δ jetScale : ℝ) (hη : 0 < η) (hηδ : η < δ) (hs : 0 < jetScale) :
    ∃ h ρ : ℝ, 0 < ρ ∧ ρ < h ∧ η < 2 * (Vb ρ * halfPlane nvec h / jetScale) ∧
      2 * (Vb ρ * halfPlane nvec h / jetScale) < δ := by
  have hH : 0 < halfPlane nvec 1 :=
    OQ14.RestrictedTEHalfPlanePositive.halfPlane_pos nvec norm_nvec 1 one_pos
  have hpi := Real.pi_pos
  set T : ℝ := (η + δ) / 2 with hT
  have hT0 : 0 < T := by rw [hT]; linarith
  have hq0 : 0 < 3 * T * jetScale / (Real.pi * halfPlane nvec 1) := by positivity
  set h : ℝ := Real.sqrt (3 * T * jetScale / (Real.pi * halfPlane nvec 1)) with hhdef
  have hh0 : 0 < h := Real.sqrt_pos.mpr hq0
  have hh2 : h ^ 2 = 3 * T * jetScale / (Real.pi * halfPlane nvec 1) := Real.sq_sqrt hq0.le
  have hp0 : 2 * (Vb (h / 2) * halfPlane nvec h / jetScale) = T := by
    unfold Vb
    rw [halfPlane_inv nvec norm_nvec h hh0]
    have hhne : h ≠ 0 := hh0.ne'
    have hHne : halfPlane nvec 1 ≠ 0 := hH.ne'
    have e1 : 2 * ((h / 2) ^ 3 * (Real.pi * 4 / 3) * (halfPlane nvec 1 / h) / jetScale) =
        Real.pi * halfPlane nvec 1 * h ^ 2 / (3 * jetScale) := by
      field_simp
      ring
    rw [e1, hh2]
    field_simp
    ring
  refine ⟨h, h / 2, by positivity, by linarith, ?_, ?_⟩
  · rw [hp0, hT]; linarith
  · rw [hp0, hT]; linarith

/-! ### Geometry for every `N` -/

/-- The points `y_l = l`. -/
def yline (N : ℕ) : Fin N → ℝ := fun l => ((l : ℕ) : ℝ)

theorem yline_injective (N : ℕ) : Function.Injective (yline N) := by
  intro i j hij
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := hij
  exact Fin.ext (by exact_mod_cast this)

theorem abovePoint_coord_one (c : PlaneInverseCube.Plane) (t : ℝ) : abovePoint c t 1 = c 1 := by
  simp [abovePoint]

theorem abovePoint_coord_zero (c : PlaneInverseCube.Plane) (t : ℝ) : abovePoint c t 0 = c 0 := by
  simp [abovePoint]

theorem abovePoint_coord_two (c : PlaneInverseCube.Plane) (t : ℝ) : abovePoint c t 2 = t := by
  simp [abovePoint]

theorem abovePoint_norm_sq (c : PlaneInverseCube.Plane) (t : ℝ) :
    ‖abovePoint c t‖ ^ 2 = (c 0) ^ 2 + (c 1) ^ 2 + t ^ 2 := by
  rw [norm_sq_space, abovePoint_coord_zero, abovePoint_coord_one, abovePoint_coord_two]

theorem yline_sep (N : ℕ) (r0 h a : ℝ) (i j : Fin N) (hij : i ≠ j) :
    1 ≤ dist (abovePoint (hpoint r0 (yline N) i) (h * a)) (abovePoint (hpoint r0 (yline N) j) (h * a)) := by
  rw [dist_eq_norm]
  have hn := PiLp.norm_apply_le (abovePoint (hpoint r0 (yline N) i) (h * a) -
    abovePoint (hpoint r0 (yline N) j) (h * a)) 1
  rw [PiLp.sub_apply, abovePoint_coord_one, abovePoint_coord_one, hpoint_one, hpoint_one, Real.norm_eq_abs] at hn
  refine le_trans ?_ hn
  change 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem yline_norm_le (N : ℕ) (r0 h a : ℝ) (hr0 : 0 ≤ r0) (hh : 0 ≤ h) (ha : 0 ≤ a) (ha1 : a ≤ 1) (l : Fin N) :
    ‖abovePoint (hpoint r0 (yline N) l) (h * a)‖ ≤ r0 + N + h := by
  have hl : ((l : ℕ) : ℝ) ≤ N := by exact_mod_cast l.is_lt.le
  have hl0 : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hha : h * a ≤ h := mul_le_of_le_one_right hh ha1
  have hha0 : 0 ≤ h * a := mul_nonneg hh ha
  have hb : 0 ≤ r0 + N + h := by linarith
  refine (sq_le_sq₀ (norm_nonneg _) hb).mp ?_
  rw [abovePoint_norm_sq, hpoint_zero, hpoint_one]
  unfold yline
  nlinarith

theorem hpoint_norm_lt (N : ℕ) (r0 : ℝ) (hr0 : 0 ≤ r0) (l : Fin N) :
    ‖hpoint r0 (yline N) l‖ < r0 + N + 1 := by
  have hl : ((l : ℕ) : ℝ) ≤ N := by exact_mod_cast l.is_lt.le
  have hl0 : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ r0 + N + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  refine (sq_lt_sq₀ (norm_nonneg _) hb).mp ?_
  rw [norm_sq_plane, hpoint_zero, hpoint_one]
  unfold yline
  nlinarith

/-- Geometry of the concrete device for every `N`: the points `y_l = l` are injective, their images at height `h a`
are at distance at least `1` (independently of `a`), and the balls lie in the ball of radius `r0 + N + 2h`. -/
theorem device_geometry (N : ℕ) (r0 h ρ : ℝ) (hr0 : 0 < r0) (hρ : 0 < ρ) (hρh : ρ < h) :
    Function.Injective (yline N) ∧
    (∀ a, 0 < a → a ≤ 1 → ∀ i j : Fin N, i ≠ j →
      1 ≤ dist (abovePoint (hpoint r0 (yline N) i) (h * a)) (abovePoint (hpoint r0 (yline N) j) (h * a))) ∧
    (∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
      ‖abovePoint (hpoint r0 (yline N) l) (h * a)‖ + ρ ≤ r0 + N + 2 * h) := by
  refine ⟨yline_injective N, fun a _ _ i j hij => yline_sep N r0 h a i j hij, ?_⟩
  intro a ha ha1 l
  have hh : 0 ≤ h := by linarith
  have := yline_norm_le N r0 h a hr0.le hh ha.le ha1 l
  linarith

/-! ### The counted-subspace theorem for fixed interpolation data -/

/-- The second stage of `concrete_doubled_counting_section`: for given interpolation data (jet scale `jetScale`,
inputs `A` with the prescribed jets, orthonormal), the counting statement of the doubled device with ball ratio
`ρ` and height `h`.  The interpolation data do not depend on `ρ`, `h`. -/
theorem doubled_counting_of_interp (r : ℝ) (hr : 0 < r) (y : ι → ℝ) (hy : Function.Injective y)
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
  have hδ' : 0 < min δ (2 * |r|) := lt_min hδ (by positivity)
  have hcdD : ∀ i j : ι ⊕ ι, i ≠ j → cD (hpoint r y) i ≠ cD (hpoint r y) j := by
    intro i j hij heq
    simp only [cD] at heq
    rcases i with l | l <;> rcases j with k | k
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) heq
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) (neg_inj.mp heq)
  exact doubled_device_counting (fun a l => abovePoint (hpoint r y l) (h * a)) ρ χ (min δ (2 * |r|)) R b (h - ρ)
    hρ hχ.le hδ' hR hb hγ hsepD (partner_hi_aux _ ρ R hi) (partner_hh_aux _ (h - ρ) ρ hh1)
    (hpoint r y) (fun _ => h) hhpos (fun a l => rfl) hcdD (fun _ => nvec) (fun _ => norm_nvec) D
    hDsym hDloc A horth hT hK (Vb ρ * halfPlane nvec h / scale) ηt δt hB hlo hhi

/-- Counted channels of the actual device for given interpolation data: the span of the interpolation family `A` is
a counted subspace for the thresholds `ηt < p0 < δt`, `p0 = 2 Vb ρ halfPlane(nvec, h) / jetScale`, eventually in
the gain index `n` and then in the shell index `r`. -/
theorem actual_counted_of_interp (r0 : ℝ) (hr0 : 0 < r0) (y : ι → ℝ) (hy : Function.Injective y)
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
    (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hhom : HomogeneousFlux Fact) (H2 : L1Interface r0 y ρ χ h R hρ hχ hi q Fact)
    (ηt δt : ℝ) (hlo : ηt < 2 * (Vb ρ * halfPlane nvec h / jetScale))
    (hhi : 2 * (Vb ρ * halfPlane nvec h / jetScale) < δt) (τ : ℝ) (hτ : τ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
          (le_max_left R 1) hi q hq n r)
        (fun a => passage volume D (Fact n r a)) (fun a => bypass volume D (Fact n r a)) τ ηt δt := by
  have hb : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hcount := doubled_counting_of_interp r0 hr0 y hy ρ χ h δ R 1 hρ hχ hh hδ hR one_ne_zero hsep hi D hDsym
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

/-! ### The final statement for every `N` and fixed thresholds -/

/-- The counted-subspace theorem of the actual device, in the form of the manuscript's `uc:counterexample`:
for every `N`, every thresholds `0 < η < δ`, every `τ ≤ 1`, every gain base `q > 1`, every `r0 > 0` and every
contrast `χ > 0` there is an explicit concrete doubled device (points `y_l = l` for `l < N`, ball ratio `ρ`, height
`h`, enclosing radius `R`, disk radius `T`) and an orthonormal family `A : Fin N → Index →0 C` of dimension `N`
such that, for every family `Fact` of plane flux densities of the actual paired-shell device that is quadratically
homogeneous and satisfies the whole-plane L1 interface with the parity flux of this device, the span of `A` is a
counted subspace (exact unit throughput, passage at least `η` times the power, absolute bypass at most `δ` times the
power) of the actual device with gain index `n` and shell index `r`, eventually in `n` and then in `r`, through the
unbounded symmetric section `{|x| > r0}` and through the bounded symmetric section `{|x| > r0} ∩ ball 0 T`. -/
theorem actual_counted_subspaces_all (N : ℕ) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1)
    (q : ℝ) (hq : 1 < q) (r0 : ℝ) (hr0 : 0 < r0) (χ : ℝ) (hχ : 0 < χ) :
    ∃ (ρ h R T : ℝ) (hρ : 0 < ρ) (_ : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint r0 (yline N) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → Idx →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      Bornology.IsBounded (Dbdd r0 T) ∧
      ∀ Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ, HomogeneousFlux Fact →
        L1Interface r0 (yline N) ρ χ h R hρ hχ hi q Fact →
        (∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint r0 (yline N) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsym r0) (Fact n r a))
            (fun a => bypass volume (Dsym r0) (Fact n r a)) τ η δ) ∧
        (∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint r0 (yline N) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dbdd r0 T) (Fact n r a))
            (fun a => bypass volume (Dbdd r0 T) (Fact n r a)) τ η δ) := by
  -- the interpolation family, chosen first: it depends only on `r0`, `y`, `χ`
  let y : Fin N → ℝ := yline N
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) := Fintype.equivFin (Fin N)
  have hy : Function.Injective y := yline_injective N
  have hr0' : r0 ≠ 0 := hr0.ne'
  have h0 : ∀ l, pts r0 y l 0 = r0 := fun l => by simp [pts, abovePoint, hpoint]
  have h1 : ∀ l, pts r0 y l 1 = y l := fun l => by simp [pts, abovePoint, hpoint]
  have h2 : ∀ l, pts r0 y l 2 = 0 := fun l => by simp [pts, abovePoint]
  obtain ⟨jetScale, hs, L, A0, _, hjet, horth0⟩ := PhysicalTEBandInterpolation.interpolate r0 hr0' y hy
    (pts r0 y) h0 h1 h2 (Fintype.card (Fin N)) (target χ e)
  -- the window, chosen after the jet scale
  obtain ⟨h, ρ, hρ, hρh, hlo, hhi⟩ := window_choice η δ jetScale hη hηδ hs
  have hgeo := device_geometry N r0 h ρ hr0 hρ hρh
  have hh0 : 0 < h := lt_trans hρ hρh
  set R : ℝ := r0 + N + 2 * h with hRdef
  have hR : 0 ≤ R := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [hRdef]
    linarith
  have hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R := hgeo.2.2
  have hsep := hgeo.2.1
  -- the transported family indexed by `Fin N`
  let e0 : Fin N ≃ Fin (Fintype.card (Fin N)) := finCongr (Fintype.card_fin N).symm
  have hrange : Set.range (A0 ∘ e0) = Set.range A0 := e0.surjective.range_comp A0
  have hli : LinearIndependent ℂ A0 :=
    LinearIndependent.of_comp (RestrictedTEInput.input : (Idx →₀ ℂ) →ₗ[ℂ] ComplexVectorSphere.Ambient) horth0.linearIndependent
  refine ⟨ρ, h, R, r0 + N + 1, hρ, hρh, hR, hi, A0 ∘ e0, horth0.comp e0 e0.injective, ?_, ?_, ?_⟩
  · rw [hrange, finrank_span_eq_card hli]
    simp
  · exact Metric.isBounded_ball.subset Set.inter_subset_right
  · intro Fact hhom H2
    rw [hrange]
    refine ⟨?_, ?_⟩
    · exact actual_counted_of_interp r0 hr0 y hy ρ χ h 1 R hρ hχ hρh one_pos hR hsep hi (Dsym r0) (Dsym_neg r0)
        (fun l => ⟨r0, hr0, fun s _ hs' => hD_sym r0 y l s hs'⟩) q hq jetScale hs A0 hjet horth0 Fact hhom H2
        η δ hlo hhi τ hτ
    · exact actual_counted_of_interp r0 hr0 y hy ρ χ h 1 R hρ hχ hρh one_pos hR hsep hi (Dbdd r0 (r0 + N + 1))
        (Dbdd_neg r0 _) (Dbdd_local r0 hr0 y _ (fun l => hpoint_norm_lt N r0 hr0.le l)) q hq jetScale hs A0 hjet
        horth0 Fact hhom H2 η δ hlo hhi τ hτ

end OQ14.RestrictedTEActualWindow
#print axioms OQ14.RestrictedTEActualWindow.halfPlane_mul
#print axioms OQ14.RestrictedTEActualWindow.halfPlane_inv
#print axioms OQ14.RestrictedTEActualWindow.window_choice
#print axioms OQ14.RestrictedTEActualWindow.yline_injective
#print axioms OQ14.RestrictedTEActualWindow.abovePoint_coord_one
#print axioms OQ14.RestrictedTEActualWindow.abovePoint_coord_zero
#print axioms OQ14.RestrictedTEActualWindow.abovePoint_coord_two
#print axioms OQ14.RestrictedTEActualWindow.abovePoint_norm_sq
#print axioms OQ14.RestrictedTEActualWindow.yline_sep
#print axioms OQ14.RestrictedTEActualWindow.yline_norm_le
#print axioms OQ14.RestrictedTEActualWindow.hpoint_norm_lt
#print axioms OQ14.RestrictedTEActualWindow.device_geometry
#print axioms OQ14.RestrictedTEActualWindow.doubled_counting_of_interp
#print axioms OQ14.RestrictedTEActualWindow.actual_counted_of_interp
#print axioms OQ14.RestrictedTEActualWindow.actual_counted_subspaces_all

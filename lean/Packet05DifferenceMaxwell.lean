import Packet05ActualLocalizedGreen
import GlobalToRegionalCurl
import WeakPoynting.ElectricControl
import MaxwellQuotientEnergy

/-! Tangential difference quotients of actual flat-interface Maxwell fields
again solve the regional Maxwell equations on the common translated region. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferenceMaxwell
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.WeakPower OQ14.CurlCutoff
  OQ14.Packet05ForcedDifferenceGreen
open scoped Topology

theorem ball_tangential_step (c x : Space) (r R h : ℝ) (i : Fin 3)
    (hx : x ∈ Metric.ball c r) (hh : |h| < R-r) :
    x + h • basis i ∈ Metric.ball c R := by
  have hb : ‖basis i‖ = 1 := by simp [basis]
  have hn : ‖h • basis i‖ = |h| := by simp [norm_smul, hb, Real.norm_eq_abs]
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  have ht : ‖x + h • basis i - c‖ ≤ ‖x-c‖ + ‖h • basis i‖ := by
    convert norm_add_le (x-c) (h • basis i) using 1; congr 1; abel
  rw [hn] at ht
  linarith

theorem cutField_global_ae {T : Set Space} (hT : IsOpen T)
    (χ : DomainCurl.Test T) (u : DomainCurl.L2Scalar T) (v : WeakCurl.L2Scalar)
    (hu : (fun x => u x) =ᵐ[DomainCurl.regionMeasure T] (fun x => v x)) :
    ElectricControl.cutField hT χ (fun _ => u) 0 =
      WeakGreen.scaleL2 χ.function χ.regular.continuous χ.compact v := by
  apply Lp.ext
  have he := extendScalar_ae T hT.measurableSet (multiply T χ.toTest (fun _ => u) 0)
  have hm := (ae_restrict_iff' hT.measurableSet).mp
    (mulL2_ae T χ.function χ.regular.continuous χ.compact u)
  have huv := (ae_restrict_iff' hT.measurableSet).mp hu
  filter_upwards [he, hm, huv, WeakGreen.scaleL2_ae χ.function χ.regular.continuous χ.compact v] with x he hm hu hv
  change extendScalar T hT.measurableSet (multiply T χ.toTest (fun _ => u) 0) x = _
  rw [he, hv]
  by_cases hx : x ∈ T
  · simp only [Set.indicator_of_mem hx]
    change mulL2 T χ.function χ.regular.continuous χ.compact u x = _
    rw [hm hx, hu hx]
  · have hz : χ.function x = 0 := by
      by_contra hn
      exact hx (χ.inside (subset_closure hn))
    simp [hx, hz]

theorem actual_tangential_difference_maxwell {Ω S T : Set Space}
    (hΩ : IsOpen Ω) (hT : IsOpen T) (κ : DomainCurl.Test Ω) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ)
    (hTleft : T ⊆ S) (hTright : ∀ x ∈ T, x + h • basis i ∈ S) :
    ∃ E' H' : DomainCurl.HCurl T,
      (∀ j, (fun x => E'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j x) ∧
      (∀ j, (fun x => H'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j x) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1)
        (FlatDifferenceCoercivity.dielectric d) E' H' := by
  let eg := LocalPower.cutExtend hΩ κ E
  let hg := LocalPower.cutExtend hΩ κ H
  have he : ∀ j, ∀ᵐ x ∂volume, x ∈ S →
      eg.val.2 j x = (Complex.I * (k : ℂ)) * hg.val.1 j x := by
    intro j
    have hc := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ κ E j)
    have hh := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ H j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp hM.1
    filter_upwards [hc, hh, hm] with x hc hh hm hx
    have hκx : κ.function x = 1 := (hκ x hx).self_of_nhds
    have hdκ : ∀ l, dcoord κ.function x l = 0 := by
      intro l
      simp [dcoord, (hκ x hx).fderiv_eq]
    rw [hc (hSΩ hx), hh (hSΩ hx), hκx, hdκ, hdκ]
    simpa using hm (hSΩ hx) j
  have hh : ∀ j, ∀ᵐ x ∂volume, x ∈ S →
      hg.val.2 j x = (-(Complex.I * (k : ℂ)) *
        (FlatDifferenceCoercivity.dielectric d x : ℂ)) * eg.val.1 j x := by
    intro j
    have hc := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ κ H j)
    have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ E j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp hM.2
    filter_upwards [hc, he, hm] with x hc he hm hx
    have hκx : κ.function x = 1 := (hκ x hx).self_of_nhds
    have hdκ : ∀ l, dcoord κ.function x l = 0 := by
      intro l
      simp [dcoord, (hκ x hx).fderiv_eq]
    rw [hc (hSΩ hx), he (hSΩ hx), hκx, hdκ, hdκ]
    simpa only [one_mul, zero_mul, add_zero, sub_zero, neg_mul] using hm (hSΩ hx) j
  have heq := localized_weight_quotient eg.val.2 hg.val.1 (fun _ => Complex.I * (k : ℂ)) S i h
    (fun _ => rfl) he
  have hw (x : Space) : (-(Complex.I * (k : ℂ)) *
      (FlatDifferenceCoercivity.dielectric d (x + h • basis i) : ℂ)) =
      (-(Complex.I * (k : ℂ)) * (FlatDifferenceCoercivity.dielectric d x : ℂ)) := by
    fin_cases i <;> simp [FlatDifferenceCoercivity.dielectric, basis, EuclideanSpace.single_apply] at hi ⊢
  have hhq := localized_weight_quotient hg.val.2 eg.val.1
    (fun x => -(Complex.I * (k : ℂ)) * (FlatDifferenceCoercivity.dielectric d x : ℂ)) S i h hw hh
  let e : WeakCurl.HCurl := ⟨(quotientVector eg.val.1 i h, quotientVector eg.val.2 i h),
    quotient_weakCurl _ _ eg.property i h⟩
  let hf : WeakCurl.HCurl := ⟨(quotientVector hg.val.1 i h, quotientVector hg.val.2 i h),
    quotient_weakCurl _ _ hg.property i h⟩
  have heT : ∀ᵐ x ∂DomainCurl.regionMeasure T, ∀ j,
      e.val.2 j x = Complex.I * (k : ℂ) * hf.val.1 j x := by
    apply ae_all_iff.mpr
    intro j
    apply (ae_restrict_iff' hT.measurableSet).mpr
    filter_upwards [heq j] with x hx hxt
    exact hx (hTleft hxt) (hTright x hxt)
  have hhT : ∀ᵐ x ∂DomainCurl.regionMeasure T, ∀ j,
      hf.val.2 j x = -(Complex.I * (k : ℂ)) *
        (FlatDifferenceCoercivity.dielectric d x : ℂ) * e.val.1 j x := by
    apply ae_all_iff.mpr
    intro j
    apply (ae_restrict_iff' hT.measurableSet).mpr
    filter_upwards [hhq j] with x hx hxt
    exact hx (hTleft hxt) (hTright x hxt)
  obtain ⟨E', H', hE', hH', hmax⟩ :=
    GlobalToRegionalCurl.restrict_weakMaxwell hT k (FlatDifferenceCoercivity.dielectric d) e hf heT hhT
  exact ⟨E', H', hE', hH', hmax⟩

/-- Caccioppoli's absorbed energy estimate applies to the actual tangential
differences, with both representatives identified above. -/
theorem actual_tangential_difference_energy {Ω S T : Set Space}
    (hΩ : IsOpen Ω) (hT : IsOpen T) (κ : DomainCurl.Test Ω) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ)
    (hTleft : T ⊆ S) (hTright : ∀ x ∈ T, x + h • basis i ∈ S)
    (ζ : WeakConservation.RealTest T) :
    ∃ E' H' : DomainCurl.HCurl T,
      (∀ j, (fun x => E'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j x) ∧
      (∀ j, (fun x => H'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j x) ∧
      (∫ x in T, ζ.function x ^ 2 * FlatDifferenceCoercivity.dielectric d x *
        OQ14.Maxwell.energy (fun j => E'.val.1 j x)) ≤
      2 * (∫ x in T, ζ.function x ^ 2 * OQ14.Maxwell.energy (fun j => H'.val.1 j x)) +
        4 / k ^ 2 * (∫ x in T, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) *
          OQ14.Maxwell.energy (fun j => H'.val.1 j x)) := by
  obtain ⟨E', H', hE, hH, hmax⟩ := actual_tangential_difference_maxwell
    hΩ hT κ hSΩ hκ k d E H hM i hi h hTleft hTright
  refine ⟨E', H', hE, hH, ?_⟩
  have hb := WeakEnergy.caccioppoli hT ζ k hk _ E' H' hmax 1 zero_lt_one ?_
  · simpa using hb
  · filter_upwards with x
    exact (FlatDifferenceCoercivity.dielectric_bounds d hd x).1

/-- Quantitative cutoff control of the actual tangential electric difference,
uniform in the step whenever the common translated region is available. -/
theorem actual_tangential_difference_cutoff_bound {Ω S T : Set Space}
    (hΩ : IsOpen Ω) (hT : IsOpen T) (κ : DomainCurl.Test Ω)
    (hκ2 : ContDiff ℝ 2 κ.function) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A)
    (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (hTleft : T ⊆ S) (hTright : ∀ x ∈ T, x + h • basis i ∈ S)
    (ζ : WeakConservation.RealTest T) (η : DomainCurl.Test T)
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C) :
    ∃ E' H' : DomainCurl.HCurl T,
      (∀ j, (fun x => E'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j x) ∧
      (∀ j, (fun x => H'.val.1 j x) =ᵐ[DomainCurl.regionMeasure T] fun x =>
        quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j x) ∧
      ‖ElectricControl.cutField hT ζ.complexTest E'.val.1‖ ≤
      Real.sqrt (3 * (2 + 4 * L ^ 2 / k ^ 2)) * (C *
        (3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
          (3 * B * ‖H.val.1‖)^2 + 1))) := by
  obtain ⟨E', H', hE, hH, hmax⟩ := actual_tangential_difference_maxwell
    hΩ hT κ hSΩ hκ k d E H hM i hi h hTleft hTright
  refine ⟨E', H', hE, hH, ?_⟩
  let Q := 3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
    (3 * B * ‖H.val.1‖)^2 + 1)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |FlatDifferenceCoercivity.dielectric d x| ≤ 1+d := by
    filter_upwards with x
    rw [abs_of_nonneg (le_trans (by norm_num) (FlatDifferenceCoercivity.dielectric_bounds d hd x).1)]
    exact (FlatDifferenceCoercivity.dielectric_bounds d hd x).2
  have hquot := MaxwellQuotientEnergy.cutoff_quotient_energy hΩ κ hκ2 hA hB
    (show 0 ≤ 1+d by linarith) hvκ hdκ k hk _ E H hM hε
  have hn : ‖ElectricControl.cutField hT η H'.val.1‖ ≤ C * Q := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hQ)).mpr
    intro j
    have heq : ElectricControl.cutField hT η H'.val.1 j =
        WeakGreen.scaleL2 η.function η.regular.continuous η.compact
          (quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j) := by
      have hhj := cutField_global_ae hT η (H'.val.1 j)
        (quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j) (hH j)
      exact hhj
    rw [heq]
    have hhbound := InteriorTestDensity.scaleL2_norm_le η.function η.regular.continuous
      η.compact (quotientVector (LocalPower.cutExtend hΩ κ H).val.1 i h j) hηbound
    exact hhbound.trans (mul_le_mul_of_nonneg_left (hquot i j h hh) hC)
  have he := ElectricControl.electric_cutoff_norm_control hT ζ η hη hζ L hgrad k hk _ E' H' hmax 1 zero_lt_one
    (Filter.Eventually.of_forall (fun x => (FlatDifferenceCoercivity.dielectric_bounds d hd x).1))
  have hfinal := he.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  simpa [Q] using hfinal

/-- One fixed ball and cutoff control all sufficiently small tangential
differences, with a bound independent of the difference step. -/
theorem actual_ball_tangential_difference_uniform {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r ≤ R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A)
    (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r)) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C) :
    ∀ (i : Fin 3), i ≠ 2 → ∀ (h : ℝ), h ≠ 0 → |h| < R-r →
      ‖(fun j => WeakGreen.scaleL2 ζ.complexTest.function
        ζ.complexTest.regular.continuous ζ.complexTest.compact
          (quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j))‖ ≤
      Real.sqrt (3 * (2 + 4 * L ^ 2 / k ^ 2)) * (C *
        (3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
          (3 * B * ‖H.val.1‖)^2 + 1))) := by
  intro i hi h hh hsmall
  have htleft : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR
  have htright : ∀ x ∈ Metric.ball c r, x + h • basis i ∈ Metric.ball c R :=
    fun x hx => ball_tangential_step c x r R h i hx hsmall
  obtain ⟨E', H', hE, hH, hbound⟩ := actual_tangential_difference_cutoff_bound
    hΩ Metric.isOpen_ball κ hκ2 hSΩ hκ A B hA hB hvκ hdκ k d hk hd E H hM
    i hi h hh htleft htright ζ η hη hζ L C hC hgrad hηbound
  have heq : ElectricControl.cutField Metric.isOpen_ball ζ.complexTest E'.val.1 =
      (fun j => WeakGreen.scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
        ζ.complexTest.compact (quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j)) := by
    funext j
    exact cutField_global_ae Metric.isOpen_ball ζ.complexTest (E'.val.1 j)
      (quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j) (hE j)
  rw [heq] at hbound
  exact hbound

/-- The cutoff field itself has uniformly bounded tangential difference
quotients; the additional term is the explicit cutoff commutator. -/
theorem actual_ball_cutoff_electric_difference_uniform {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r ≤ R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A)
    (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r)) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∀ (i : Fin 3), i ≠ 2 → ∀ (h : ℝ), h ≠ 0 → |h| < R-r → ∀ (j : Fin 3),
      ‖MaxwellDifferenceQuotient.quotient
        (WeakGreen.scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
          ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)) i h‖ ≤
      Real.sqrt (3 * (2 + 4 * L ^ 2 / k ^ 2)) * (C *
        (3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
          (3 * B * ‖H.val.1‖)^2 + 1))) +
        3*D*‖(LocalPower.cutExtend hΩ κ E).val.1 j‖ := by
  intro i hi h hh hsmall j
  have hb := actual_ball_tangential_difference_uniform hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C hC hgrad hηbound i hi h hh hsmall
  have hj := norm_le_pi_norm (fun j => WeakGreen.scaleL2 ζ.complexTest.function
    ζ.complexTest.regular.continuous ζ.complexTest.compact
      (quotientVector (LocalPower.cutExtend hΩ κ E).val.1 i h j)) j
  rw [MaxwellCutoffCommutator.cutoff_quotient_decomposition ζ.complexTest.toTest
    ((LocalPower.cutExtend hΩ κ E).val.1 j) i h hh D hζder]
  exact (norm_add_le _ _).trans (add_le_add (hj.trans hb)
    (MaxwellCutoffCommutator.cutoffSource_norm ζ.complexTest.toTest _ i h hh D hζder))

end OQ14.Packet05DifferenceMaxwell
#print axioms OQ14.Packet05DifferenceMaxwell.actual_tangential_difference_maxwell
#print axioms OQ14.Packet05DifferenceMaxwell.actual_tangential_difference_energy
#print axioms OQ14.Packet05DifferenceMaxwell.cutField_global_ae
#print axioms OQ14.Packet05DifferenceMaxwell.actual_tangential_difference_cutoff_bound
#print axioms OQ14.Packet05DifferenceMaxwell.ball_tangential_step
#print axioms OQ14.Packet05DifferenceMaxwell.actual_ball_tangential_difference_uniform
#print axioms OQ14.Packet05DifferenceMaxwell.actual_ball_cutoff_electric_difference_uniform

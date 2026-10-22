import ConicalAngularTests
import ConicalPolarTests

/-! Actual compact spatial test radii, local integrability, and derivative pairing Fubini. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalSpatialTests
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
open scoped Topology ENNReal

theorem potential_locallyIntegrable (ν a t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : LocallyIntegrable (potential ν a t) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space) R).measure_ne_top
  have hi : IntegrableOn (potential ν a t) (closedBall 0 R) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (potential_memLp_two_ball ν a t R hν ha ht ht1)
  exact hi.mono_set hR

theorem electric_locallyIntegrable (ν a t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : LocallyIntegrable (electric ν a t) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space) R).measure_ne_top
  have hi : IntegrableOn (electric ν a t) (closedBall 0 R) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (electric_memLp_two_ball ν a t R hν ha ht ht1)
  exact hi.mono_set hR

theorem electric_component_locallyIntegrable (ν a t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) : LocallyIntegrable (fun x => electric ν a t x i) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integrable_comp
    ((electric_locallyIntegrable ν a t hν ha ht ht1).integrableOn_isCompact hK)

theorem compact_test_radius (ψ : Space → ℝ) (hcompact : HasCompactSupport ψ) :
    ∃ R > (0 : ℝ), ∀ r ≥ R, ∀ n : Sphere,
      ψ (r • (n : Space)) = 0 ∧ fderiv ℝ ψ (r • (n : Space)) = 0 := by
  obtain ⟨B,hB⟩ := hcompact.isBounded.subset_closedBall (0 : Space)
  refine ⟨max B 1+1,by linarith [le_max_right B (1 : ℝ)],fun r hr n => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith [le_max_right B (1 : ℝ)]) hr
  have hn : r • (n : Space) ∉ tsupport ψ := by
    intro hx
    have h := hB hx
    rw [mem_closedBall,dist_zero_right,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos hr0,mul_one] at h
    linarith [le_max_left B (1 : ℝ)]
  exact ⟨image_eq_zero_of_nmem_tsupport hn,fderiv_of_not_mem_tsupport ℝ hn⟩

theorem integral_Ioi_truncate (f : ℝ → ℝ) (R : ℝ) (hf : ∀ r ≥ R, f r = 0) :
    (∫ r in Ioi (0 : ℝ), f r) = ∫ r in Ioo (0 : ℝ) R, f r := by
  have h := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := Iio R) (f := f)
    (fun r hr => hf r (le_of_not_gt hr))
  simpa only [Measure.restrict_restrict measurableSet_Iio,Iio_inter_Ioi] using h.symm

theorem derivative_product_integrable (R : ℝ) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo (0 : ℝ) R)) (H : Sphere → ℝ) (hH : Integrable H angularMeasure)
    (V : Sphere → Space) (hV : Continuous V) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hcompact : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × Sphere => f p.1*H p.2*fderiv ℝ ψ (p.1 • (p.2 : Space)) (V p.2))
      ((volume.restrict (Ioo (0 : ℝ) R)).prod angularMeasure) := by
  obtain ⟨C,hC⟩ := (hcompact.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv le_rfl)
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
  have hc : Continuous (fun p : ℝ × Sphere => fderiv ℝ ψ (p.1 • (p.2 : Space)) (V p.2)) :=
    ((hψ.continuous_fderiv le_rfl).comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).clm_apply
      (hV.comp continuous_snd)
  apply ((hf.norm.mul_prod hH.norm).const_mul (|C| * |B|)).mono'
    ((hf.aestronglyMeasurable.fst.mul hH.aestronglyMeasurable.snd).mul hc.aestronglyMeasurable)
  filter_upwards with p
  change ‖f p.1*H p.2*fderiv ℝ ψ (p.1 • (p.2 : Space)) (V p.2)‖ ≤
    (|C| * |B|)*(‖f p.1‖*‖H p.2‖)
  have hb : ‖fderiv ℝ ψ (p.1 • (p.2 : Space)) (V p.2)‖ ≤ |C| * |B| := by
    exact ((fderiv ℝ ψ _).le_opNorm _).trans (mul_le_mul
      ((hC _).trans (le_abs_self C)) ((hB _ (mem_univ _)).trans (le_abs_self B)) (norm_nonneg _) (abs_nonneg _))
  rw [norm_mul,norm_mul]
  calc
    ‖f p.1‖*‖H p.2‖*‖fderiv ℝ ψ (p.1 • (p.2 : Space)) (V p.2)‖ ≤ ‖f p.1‖*‖H p.2‖*(|C| * |B|) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (|C| * |B|)*(‖f p.1‖*‖H p.2‖) := by ring

theorem power_derivative_swap (β R : ℝ) (hβ : -1 < β) (hR : 0 < R)
    (H : Sphere → ℝ) (hH : Integrable H angularMeasure) (V : Sphere → Space) (hV : Continuous V)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^β*H n*fderiv ℝ ψ (r • (n : Space)) (V n) ∂angularMeasure) =
      ∫ n : Sphere, (∫ r in Ioo (0 : ℝ) R, r^β*H n*fderiv ℝ ψ (r • (n : Space)) (V n)) ∂angularMeasure := by
  apply integral_integral_swap
  apply derivative_product_integrable R (fun r : ℝ => r^β) _ H hH V hV ψ hψ hcompact
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mp
    (intervalIntegral.intervalIntegrable_rpow' hβ)

end OQ14.ConicalSpatialTests

#print axioms OQ14.ConicalSpatialTests.potential_locallyIntegrable
#print axioms OQ14.ConicalSpatialTests.electric_locallyIntegrable
#print axioms OQ14.ConicalSpatialTests.electric_component_locallyIntegrable
#print axioms OQ14.ConicalSpatialTests.compact_test_radius
#print axioms OQ14.ConicalSpatialTests.integral_Ioi_truncate
#print axioms OQ14.ConicalSpatialTests.derivative_product_integrable
#print axioms OQ14.ConicalSpatialTests.power_derivative_swap

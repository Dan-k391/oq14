import Packet06ConeRenormalized
import Packet06ConeUniformParticular
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeMomentCancellation
open Set MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData
  OQ14.ConicalMomentWeights OQ14.PolarMomentTesting

theorem correction_origin_identity (p : ConicalStaticVolume.Data) (a : ℝ) (s : System p a) :
    tangentCorrection s 0 = (p.eigenvalue : ℂ)*radialCorrection s 0 := by
  have hweight (i : Fin 3) :
      (∫ n : Sphere, tangent p.eigenvalue p.contrast p.threshold i n ∂angularMeasure) =
      (p.eigenvalue : ℂ) * ∫ n : Sphere, radial p.eigenvalue p.contrast p.threshold i n ∂angularMeasure := by
    have h := Packet06ConeConstantCorrection.angular_constant_identity p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one p.angular_root i
    have hc := congrArg Complex.ofReal h
    simp only [Complex.ofReal_mul] at hc
    have ht : (∫ n : Sphere, tangent p.eigenvalue p.contrast p.threshold i n ∂angularMeasure) =
        ((∫ n : Sphere, CapSturmLiouville.coefficient p.contrast p.threshold ((n : Maxwell.Space) 2) *
          SphereCapH1.gradient p.eigenvalue p.threshold n i ∂angularMeasure) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with n
      simp [tangent]
    have hr : (∫ n : Sphere, radial p.eigenvalue p.contrast p.threshold i n ∂angularMeasure) =
        ((∫ n : Sphere, CapSturmLiouville.coefficient p.contrast p.threshold ((n : Maxwell.Space) 2) *
          SphereCapH1.field p.eigenvalue p.threshold n * (n : Maxwell.Space) i ∂angularMeasure) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with n
      simp [radial,scalar,ConicalRadialDivergence.angularWeight, mul_assoc]
    rw [ht,hr]
    have hi₁ := integral_ofReal (𝕜 := ℂ) (μ := angularMeasure) (f := fun n : Sphere =>
      CapSturmLiouville.coefficient p.contrast p.threshold ((n : Maxwell.Space) 2) *
        SphereCapH1.gradient p.eigenvalue p.threshold n i)
    have hi₂ := integral_ofReal (𝕜 := ℂ) (μ := angularMeasure) (f := fun n : Sphere =>
      CapSturmLiouville.coefficient p.contrast p.threshold ((n : Maxwell.Space) 2) *
        SphereCapH1.field p.eigenvalue p.threshold n * (n : Maxwell.Space) i)
    push_cast at hi₁ hi₂
    exact hi₁.trans (hc.trans (congrArg (fun z : ℂ => (p.eigenvalue : ℂ)*z) hi₂.symm))
  simp only [tangentCorrection,radialCorrection,moment,zero_smul,integral_const_mul,
    Finset.mul_sum,hweight]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem moment_sub_origin (f : Maxwell.Space → ℂ) (hf : Continuous f)
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C) (r : ℝ) :
    moment f σ r - moment f σ 0 = moment (fun x => f x-f 0) σ r := by
  have hbound : ∃ M : ℝ, ∀ n : Sphere, ‖f (r • (n : Maxwell.Space))‖ ≤ M := by
    have hc : IsCompact (Set.range (fun n : Sphere => r • (n : Maxwell.Space))) :=
      by simpa only [Set.image_univ] using isCompact_univ.image (continuous_const.smul continuous_subtype_val : Continuous (fun n : Sphere => r • (n : Maxwell.Space)))
    obtain ⟨M,hM⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨M,fun n => hM _ ⟨n,rfl⟩⟩
  obtain ⟨M,hM⟩ := hbound
  have hi : Integrable (fun n : Sphere => f (r • (n : Maxwell.Space))*σ n) angularMeasure := by
    apply (integrable_const (M*C)).mono'
      (((hf.comp (continuous_const.smul continuous_subtype_val)).measurable.mul hσ).aestronglyMeasurable)
    filter_upwards with n
    rw [norm_mul]
    exact mul_le_mul (hM n) (hC n) (norm_nonneg _) ((norm_nonneg _).trans (hM n))
  have hi0 : Integrable (fun n : Sphere => f 0*σ n) angularMeasure := by
    apply (integrable_const (‖f 0‖*C)).mono' (measurable_const.mul hσ).aestronglyMeasurable
    filter_upwards with n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
  simp only [moment,zero_smul,← integral_sub hi hi0]
  apply integral_congr_ae
  filter_upwards with n
  ring

theorem moment_difference_holder (p : ConicalStaticVolume.Data) (a R M α C : ℝ) (s : System p a)
    (hM : 0 ≤ M) (_hα : 0 < α) (_hC : 0 ≤ C)
    (hW : ∀ i x, x ∈ Metric.closedBall (0 : Maxwell.Space) R → ‖s.correction i x-s.correction i 0‖ ≤ M*‖x‖^α)
    (hrw : ∀ i n, ‖radial p.eigenvalue p.contrast p.threshold i n‖ ≤ C)
    (htw : ∀ i n, ‖tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ C)
    (r : ℝ) (hri : r ∈ Icc (0 : ℝ) R) :
    ‖radialCorrection s r-radialCorrection s 0‖ ≤ (3*C*(angularMeasure univ).toReal*M)*r^α ∧
      ‖tangentCorrection s r-tangentCorrection s 0‖ ≤ (3*C*(angularMeasure univ).toReal*M)*r^α := by
  have hm : 0 ≤ M*r^α := mul_nonneg hM (Real.rpow_nonneg hri.1 _)
  have hb (σ : Fin 3 → Sphere → ℂ) (hσ : ∀ i, Measurable (σ i)) (hw : ∀ i n, ‖σ i n‖ ≤ C) :
      ‖(∑ i : Fin 3, moment (s.correction i) (σ i) r) - ∑ i : Fin 3, moment (s.correction i) (σ i) 0‖ ≤
        (3*C*(angularMeasure univ).toReal*M)*r^α := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [moment_sub_origin _ (s.continuous _) _ (hσ _) C (hw _) r]
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (fun x => s.correction i x-s.correction i 0) (σ i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, (M*r^α)*C*(angularMeasure univ).toReal := by
        apply Finset.sum_le_sum
        intro i _
        apply PolarMomentContinuity.moment_norm_le _ (σ i) (M*r^α) C hm (hw i) r
        intro n
        have hn : r • (n : Maxwell.Space) ∈ Metric.closedBall 0 R := by
          simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
            abs_of_nonneg hri.1,sphere_norm,mul_one] using hri.2
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hri.1,sphere_norm,mul_one] using hW i _ hn
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  exact ⟨hb _ (fun i => radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) hrw,
    hb _ (fun i => tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) htw⟩

#print axioms OQ14.Packet06ConeMomentCancellation.correction_origin_identity
#print axioms OQ14.Packet06ConeMomentCancellation.moment_sub_origin
#print axioms OQ14.Packet06ConeMomentCancellation.moment_difference_holder
end OQ14.Packet06ConeMomentCancellation

import ComplexScalarFar
import DyadicRadiation
import MaxwellFarField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexDyadicOutgoing
open Complex MeasureTheory Metric Filter OQ14.Maxwell OQ14.ComplexGreenKernel
  OQ14.DyadicRadiation
open scoped Topology InnerProductSpace

theorem dyadic_factorization (z : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    ComplexDynamicKernel.dyadic z x i j = phi z x *
      (z^2 * transverse x i j +
        (I*z / ‖x‖ - 1 / (‖x‖ : ℂ)^2) *
          ((if i = j then 1 else 0) - 3 * GreenKernel.unitCoordinate i x * GreenKernel.unitCoordinate j x)) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold ComplexDynamicKernel.dyadic phi phiHessian radial radialD radialDD transverse GreenKernel.unitCoordinate
  push_cast
  generalize hrr : (‖x‖ : ℂ) = r at hr ⊢
  generalize hpp : (Real.pi : ℂ) = p at hp ⊢
  split_ifs <;> field_simp (maxDischargeDepth := 100) [hr, hp]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

theorem ray_distance_tendsto (n y : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => ‖r • n-y‖) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-‖y‖) tendsto_id)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have h := norm_sub_norm_le (r • n) y
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one] at h
  simpa only [sub_eq_add_neg] using h

theorem ray_transverse_limit (n y : Space) (hn : ‖n‖ = 1) (i j : Fin 3) :
    Tendsto (fun r : ℝ => transverse (r • n-y) i j) atTop (𝓝 (transverse n i j)) := by
  have hi := tendsto_inv_atTop_zero.comp (ray_distance_tendsto n y hn)
  have hb : Tendsto (fun r : ℝ => (4*‖y‖) * (‖r • n-y‖)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hi.const_mul (4*‖y‖)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_gt_atTop (‖y‖), eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hx : r • n ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simp [norm_smul, hn, abs_of_pos hr0, hr0.ne']
  have hz : r • n-y ≠ 0 := by
    intro he
    have hh := norm_sub_norm_le (r • n) y
    rw [he, norm_zero] at hh
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hn, mul_one] at hh
    linarith
  have h := transverse_difference (r • n) (r • n-y) hx hz i j
  have ht := MaxwellFarField.ray_transverse n hn r hr0 i j
  rw [ht, show (r • n-y)-(r • n) = -y by abel, norm_neg] at h
  simpa only [div_eq_mul_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

theorem correction_limit (z : ℂ) (n y : Space) (hn : ‖n‖ = 1) (i j : Fin 3) :
    Tendsto (fun r : ℝ =>
      (I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2) *
        ((if i = j then 1 else 0) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
          GreenKernel.unitCoordinate j (r • n-y))) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℝ => ((‖r • n-y‖)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (ray_distance_tendsto n y hn)
  have hc : Tendsto (fun r : ℝ => (((‖r • n-y‖)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp hi
  have ha : Tendsto (fun r : ℝ => I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2) atTop (𝓝 0) := by
    convert (hc.const_mul (I*z)).sub (hc.pow 2) using 1 <;>
      simp [div_eq_mul_inv, ofReal_inv, inv_pow]
  have hb : Tendsto (fun r : ℝ => ‖I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2‖ * 4) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_mul] using ha.norm.mul_const 4
  apply squeeze_zero_norm' _ hb
  filter_upwards with r
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hu : ‖(3 : ℂ) * GreenKernel.unitCoordinate i (r • n-y) * GreenKernel.unitCoordinate j (r • n-y)‖ ≤ 3 := by
    simp only [norm_mul, Complex.norm_ofNat]
    have hm := mul_le_mul (ScalarRadiation.unitCoordinate_norm_le i (r • n-y))
      (ScalarRadiation.unitCoordinate_norm_le j (r • n-y)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have ht : ‖(if i = j then 1 else 0 : ℂ) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
      GreenKernel.unitCoordinate j (r • n-y)‖ ≤ 4 := (norm_sub_le _ _).trans (by linarith)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem scaled_dyadic_limit (z : ℂ) (n y : Space) (hn : ‖n‖ = 1) (i j : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-I*z*r) *
      ComplexDynamicKernel.dyadic z (r • n-y) i j) atTop
      (𝓝 ((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ)) / (4*Real.pi)) *
        (z^2 * transverse n i j))) := by
  have hs := ComplexScalarFar.scaledKernel_limit z n y hn
  have ht := (ray_transverse_limit n y hn i j).const_mul (z^2)
  have hc := correction_limit z n y hn i j
  have h := hs.mul (ht.add hc)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (‖y‖), eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hx : r • n-y ≠ 0 := by
    intro he
    have hh := norm_sub_norm_le (r • n) y
    rw [he, norm_zero] at hh
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hn, mul_one] at hh
    linarith
  rw [dyadic_factorization z _ hx]
  simp only [ComplexScalarFar.scaledKernel]
  ring

theorem scaled_dyadic_bound (z : ℂ) (R r : ℝ) (hR : 0 ≤ R) (hr : 2*R < r) (hr2 : 2 ≤ r)
    (n y : Space) (hn : ‖n‖ = 1) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖(r : ℂ) * Complex.exp (-I*z*r) * ComplexDynamicKernel.dyadic z (r • n-y) i j‖ ≤
      (2 * Real.exp (‖z‖*R) / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1)) := by
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hyb : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hd := abs_norm_sub_norm_le (r • n-y) (r • n)
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  rw [hnr, show r • n-y-r • n = -y by abel, norm_neg] at hd
  have hdist : 1 ≤ ‖r • n-y‖ := by
    have hh := (abs_sub_le_iff.mp (hd.trans hyb)).2
    linarith
  have hx : r • n-y ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖r • n-y‖ ≠ 0)
  have hinv : (‖r • n-y‖)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < ‖r • n-y‖)).mpr hdist
  have ha : ‖I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2‖ ≤ ‖z‖+1 := by
    apply (norm_sub_le _ _).trans
    simp only [div_eq_mul_inv, norm_mul, norm_inv, norm_I, one_mul, norm_one, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_pow]
    have h0 : 0 ≤ (‖r • n-y‖)⁻¹ := by positivity
    have hi2 : (‖r • n-y‖^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left hinv (norm_nonneg z)]
  have hd0 : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hu : ‖(3 : ℂ) * GreenKernel.unitCoordinate i (r • n-y) * GreenKernel.unitCoordinate j (r • n-y)‖ ≤ 3 := by
    simp only [norm_mul, Complex.norm_ofNat]
    have hm := mul_le_mul (ScalarRadiation.unitCoordinate_norm_le i (r • n-y))
      (ScalarRadiation.unitCoordinate_norm_le j (r • n-y)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hb : ‖(if i = j then 1 else 0 : ℂ) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
      GreenKernel.unitCoordinate j (r • n-y)‖ ≤ 4 := (norm_sub_le _ _).trans (by linarith)
  have ht := transverse_norm_bound (r • n-y) i j
  have hfactor : ‖z^2 * transverse (r • n-y) i j +
      (I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2) *
        ((if i = j then 1 else 0) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
          GreenKernel.unitCoordinate j (r • n-y))‖ ≤ 2*‖z‖^2 + 4*(‖z‖+1) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow]
    have h1 := mul_le_mul_of_nonneg_left ht (sq_nonneg ‖z‖)
    have h2 := mul_le_mul ha hb (norm_nonneg _) (by positivity : 0 ≤ ‖z‖+1)
    nlinarith
  rw [dyadic_factorization z _ hx]
  have he : (r : ℂ) * Complex.exp (-I*z*r) * (phi z (r • n-y) *
      (z^2 * transverse (r • n-y) i j +
      (I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2) *
        ((if i = j then 1 else 0) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
          GreenKernel.unitCoordinate j (r • n-y)))) =
      ComplexScalarFar.scaledKernel z r n y *
        (z^2 * transverse (r • n-y) i j +
        (I*z / (‖r • n-y‖ : ℂ) - 1 / (‖r • n-y‖ : ℂ)^2) *
          ((if i = j then 1 else 0) - 3 * GreenKernel.unitCoordinate i (r • n-y) *
            GreenKernel.unitCoordinate j (r • n-y))) := by
    simp only [ComplexScalarFar.scaledKernel]
    ring
  rw [he, norm_mul]
  exact mul_le_mul (ComplexScalarFar.scaledKernel_bound z R r hR hr n y hn hy) hfactor
    (norm_nonneg _) (by positivity)

theorem dyadic_measurable (z : ℂ) (i j : Fin 3) :
    Measurable (fun x => ComplexDynamicKernel.dyadic z x i j) := by
  unfold ComplexDynamicKernel.dyadic phi phiHessian radial radialD radialDD
  fun_prop

def amplitude (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2) (n : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ComplexScalarFar.amplitude z (DynamicVolume.source c u j) n * (z^2 * transverse n i j)

theorem field_far_limit (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-I*z*r) *
      ComplexExteriorIntegral.field c z u (r • n) i) atTop (𝓝 (amplitude c z u n i)) := by
  have hlim (j : Fin 3) : Tendsto (fun r : ℝ => ∫ y,
      DynamicVolume.source c u j y * ((r : ℂ) * Complex.exp (-I*z*r) *
        ComplexDynamicKernel.dyadic z (r • n-y) i j)) atTop
      (𝓝 (∫ y, DynamicVolume.source c u j y *
        ((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ)) / (4*Real.pi)) * (z^2 * transverse n i j)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun y => ‖DynamicVolume.source c u j y‖ *
        ((2 * Real.exp (‖z‖*R) / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1))))
    · apply Eventually.of_forall
      intro r
      apply (DynamicVolume.source_integrable c u R hc j).aestronglyMeasurable.mul
      apply AEStronglyMeasurable.const_mul
      exact ((dyadic_measurable z i j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (2*R), eventually_ge_atTop (2 : ℝ)] with r hr hr2
      filter_upwards with y
      by_cases hy : y ∈ closedBall (0 : Space) R
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (scaled_dyadic_bound z R r hR hr hr2 n y hn hy i j) (norm_nonneg _)
      · simp [DynamicVolume.source_zero c u R hc j y hy]
    · exact (DynamicVolume.source_integrable c u R hc j).norm.mul_const _
    · filter_upwards with y
      exact tendsto_const_nhds.mul (scaled_dyadic_limit z n y hn i j)
  have h := tendsto_finset_sum Finset.univ (fun j _ => hlim j)
  have ha (j : Fin 3) : (∫ y, DynamicVolume.source c u j y *
        ((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ)) / (4*Real.pi)) * (z^2 * transverse n i j))) =
      ComplexScalarFar.amplitude z (DynamicVolume.source c u j) n * (z^2 * transverse n i j) := by
    rw [ComplexScalarFar.amplitude, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    ring
  simp_rw [ha] at h
  apply h.congr'
  filter_upwards with r
  simp only [ComplexExteriorIntegral.field, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

#print axioms OQ14.ComplexDyadicOutgoing.field_far_limit
#print axioms OQ14.ComplexDyadicOutgoing.scaled_dyadic_bound
#print axioms OQ14.ComplexDyadicOutgoing.scaled_dyadic_limit
#print axioms OQ14.ComplexDyadicOutgoing.correction_limit
#print axioms OQ14.ComplexDyadicOutgoing.ray_distance_tendsto
#print axioms OQ14.ComplexDyadicOutgoing.ray_transverse_limit
#print axioms OQ14.ComplexDyadicOutgoing.dyadic_factorization
end OQ14.ComplexDyadicOutgoing










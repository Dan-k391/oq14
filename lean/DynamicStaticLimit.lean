import DynamicVolumeConstants
import Mathlib.Algebra.Ring.Invertible

/-! Quantitative zero-frequency convergence of the actual Maxwell material volume inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.DynamicStaticLimit
open Filter OQ14.DynamicVolume
open scoped Topology

def size (c : Coefficient) (R : ℝ) : ℝ := 252*c.bound*R^2
def frequencyRadius (c : Coefficient) (R : ℝ) : ℝ := (2*(1+size c R))⁻¹

theorem size_nonnegative (c : Coefficient) (R : ℝ) : 0 ≤ size c R := by
  unfold size
  exact mul_nonneg (mul_nonneg (by norm_num) (StaticCoefficient.bound_nonnegative c)) (sq_nonneg R)

theorem frequencyRadius_positive (c : Coefficient) (R : ℝ) : 0 < frequencyRadius c R := by
  have h := size_nonnegative c R
  unfold frequencyRadius
  positivity

theorem error_small (c : Coefficient) (k R : ℝ) (hk : |k| ≤ frequencyRadius c R) :
    errorBound c k R ≤ 1/2 := by
  have hC := size_nonnegative c R
  have hd : 0 < 2*(1+size c R) := by positivity
  have hrad : frequencyRadius c R ≤ 1 := by
    unfold frequencyRadius
    exact (inv_le_one₀ hd).mpr (by linarith)
  have hk1 : |k| ≤ 1 := hk.trans hrad
  have hk2 : k^2 ≤ |k| := by nlinarith [sq_abs k,abs_nonneg k]
  have hm : |k| * (2*(1+size c R)) ≤ 1 :=
    (le_div_iff₀ hd).mp (by simpa only [frequencyRadius,one_div] using hk)
  rw [errorBound_explicit]
  change 252*c.bound*k^2*R^2 ≤ _
  have ht := mul_le_mul_of_nonneg_left hk2 hC
  dsimp only [size] at ht hm hC
  nlinarith [abs_nonneg k]

theorem inverse_norm_two (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ frequencyRadius c R) : ‖Ring.inverse (volumeBlock c k R)‖ ≤ 2 := by
  have he := error_small c k R hk
  apply (volumeBlock_inverse_bound c k R hR (by linarith)).trans
  rw [← one_div]
  exact (div_le_iff₀ (by linarith : 0 < 1-errorBound c k R)).mpr (by linarith)

theorem inverse_difference_bound (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ frequencyRadius c R) :
    ‖Ring.inverse (volumeBlock c k R)-Ring.inverse (StaticNewton.volumeBlock c)‖ ≤
      2*size c R*k^2 := by
  have he := error_small c k R hk
  have ha := volumeBlock_isUnit c k R hR (by linarith)
  have hb := StaticNewton.volumeBlock_isUnit c
  rw [Ring.inverse_sub_inverse ⟨fun _ => hb,fun _ => ha⟩]
  have hsub : StaticNewton.volumeBlock c-volumeBlock c k R=weightedRemainder c k R := by
    unfold volumeBlock
    abel
  rw [hsub]
  calc
    _ ≤ ‖Ring.inverse (volumeBlock c k R)‖*‖weightedRemainder c k R‖*
        ‖Ring.inverse (StaticNewton.volumeBlock c)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 2*errorBound c k R*1 := by
      exact mul_le_mul (mul_le_mul (inverse_norm_two c k R hR hk)
        (weightedRemainder_norm_le c k R hR) (norm_nonneg _) (by norm_num))
        (StaticNewton.volumeBlock_inverse_norm_le c) (norm_nonneg _)
        (mul_nonneg (by norm_num) (errorBound_nonnegative c k R))
    _ = _ := by rw [errorBound_explicit]; unfold size; ring

theorem inverse_tendsto (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun k : ℝ => Ring.inverse (volumeBlock c k R)) (𝓝 0)
      (𝓝 (Ring.inverse (StaticNewton.volumeBlock c))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : ∀ᶠ k : ℝ in 𝓝 0, ‖Ring.inverse (volumeBlock c k R)-
      Ring.inverse (StaticNewton.volumeBlock c)‖ ≤ 2*size c R*k^2 := by
    have hδ := frequencyRadius_positive c R
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with k hk
    apply inverse_difference_bound c k R hR
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hk : |k| < frequencyRadius c R).le
  have hl : Tendsto (fun k : ℝ => 2*size c R*k^2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 0) (𝓝 0)).pow 2))
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) he hl

theorem solution_comparison (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ frequencyRadius c R) (f f0 : VectorL2) :
    ‖Ring.inverse (volumeBlock c k R) f-Ring.inverse (StaticNewton.volumeBlock c) f0‖ ≤
      2*‖f-f0‖+2*size c R*k^2*‖f0‖ := by
  have he : Ring.inverse (volumeBlock c k R) f-Ring.inverse (StaticNewton.volumeBlock c) f0=
      Ring.inverse (volumeBlock c k R) (f-f0)+
        (Ring.inverse (volumeBlock c k R)-Ring.inverse (StaticNewton.volumeBlock c)) f0 := by
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (inverse_norm_two c k R hR hk) (norm_nonneg _)))
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (inverse_difference_bound c k R hR hk) (norm_nonneg _)))

end OQ14.DynamicStaticLimit

#print axioms OQ14.DynamicStaticLimit.size_nonnegative
#print axioms OQ14.DynamicStaticLimit.frequencyRadius_positive
#print axioms OQ14.DynamicStaticLimit.error_small
#print axioms OQ14.DynamicStaticLimit.inverse_norm_two
#print axioms OQ14.DynamicStaticLimit.inverse_difference_bound
#print axioms OQ14.DynamicStaticLimit.inverse_tendsto
#print axioms OQ14.DynamicStaticLimit.solution_comparison

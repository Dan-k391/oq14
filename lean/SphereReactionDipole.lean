import SphereReactionLipschitz
import StaticBallDipole

/-! Actual reaction integrals, source moments, and dipole errors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.SphereReactionDipole

open MeasureTheory Metric SphereReactionKernel
open scoped Topology

theorem integrand_integrable (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (f : Space → ℂ) (hf : Integrable f) :
    Integrable (fun y => reaction electric k x y i j*f y) :=
  hf.bdd_mul' ((reaction_continuous electric k i j).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => reaction_bound electric k x y i j))

theorem integral_bound (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (f : Space → ℂ) (hf : Integrable f) :
    ‖∫ y, reaction electric k x y i j*f y‖ ≤ entryBound k*(∫ y, ‖f y‖) := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (integrand_integrable electric k x i j f hf).norm
    (hf.norm.const_mul (entryBound k))
  filter_upwards with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (reaction_bound electric k x y i j) (norm_nonneg _)

theorem integral_difference_bound (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (f g : Space → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ y, reaction electric k x y i j*f y)-(∫ y, reaction electric k x y i j*g y)‖ ≤
      entryBound k*(∫ y, ‖f y-g y‖) := by
  have he : (∫ y, reaction electric k x y i j*f y)-(∫ y, reaction electric k x y i j*g y) =
      ∫ y, reaction electric k x y i j*(f y-g y) := by
    rw [← integral_sub (integrand_integrable electric k x i j f hf)
      (integrand_integrable electric k x i j g hg)]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [he]
  exact integral_bound electric k x i j (fun y => f y-g y) (hf.sub hg)

theorem moment_error (electric : Bool) (k : ℝ) (x c : Space) (R : ℝ)
    (i j : Fin 3) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, R < ‖y-c‖ → f y=0) :
    ‖(∫ y, reaction electric k x y i j*f y)-reaction electric k x c i j*(∫ y, f y)‖ ≤
      SphereReactionLipschitz.bound k*R*(∫ y, ‖f y‖) := by
  have hi := integrand_integrable electric k x i j f hf
  have hc := hf.const_mul (reaction electric k x c i j)
  have he : (∫ y, reaction electric k x y i j*f y)-reaction electric k x c i j*(∫ y, f y) =
      ∫ y, (reaction electric k x y i j-reaction electric k x c i j)*f y := by
    rw [← integral_const_mul, ← integral_sub hi hc]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae ((hi.sub hc).congr (Filter.Eventually.of_forall
    (fun y => by dsimp; ring))).norm (hf.norm.const_mul _)
  filter_upwards [hs] with y hy
  rw [norm_mul]
  by_cases hout : R < ‖y-c‖
  · rw [hy hout, norm_zero, mul_zero, mul_zero]
  · have hd := SphereReactionLipschitz.reaction_source_difference electric k x y c i j
    exact mul_le_mul_of_nonneg_right
      (hd.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hout)
        (SphereReactionLipschitz.bound_nonnegative k))) (norm_nonneg _)

theorem ball_source_error (electric : Bool) (k : ℝ) (x c : Space) (R : ℝ)
    (P : StaticBallNewton.Vector) (i j : Fin 3) :
    ‖(∫ y, reaction electric k x y i j*
        StaticBallCentered.source c R P (VectorFourier.coordinateMap y) j)-
      reaction electric k x c i j*((volume.real (ball c R) : ℂ)*P j)‖ ≤
      SphereReactionLipschitz.bound k*R*(volume.real (ball c R)*‖P j‖) := by
  have hs : ∀ᵐ y : Space, R < ‖y-c‖ →
      StaticBallCentered.source c R P (VectorFourier.coordinateMap y) j=0 := by
    filter_upwards [StaticBallCentered.source_ae c R P j] with y hy hout
    have hyout : y ∉ ball c R := by
      simpa only [mem_ball, dist_eq_norm] using (not_lt.mpr hout.le)
    rw [hy, Set.indicator_of_not_mem hyout]
  have hm : (∫ y, ‖StaticBallCentered.source c R P (VectorFourier.coordinateMap y) j‖) =
      volume.real (ball c R)*‖P j‖ := by
    calc
      _ = ∫ y, ‖(ball c R).indicator (fun _ => P j) y‖ := by
        apply integral_congr_ae
        filter_upwards [StaticBallCentered.source_ae c R P j] with y hy
        rw [hy]
      _ = _ := by
        simp only [norm_indicator_eq_indicator_norm]
        rw [integral_indicator_const _ measurableSet_ball]
        rfl
  have he := moment_error electric k x c R i j
    (fun y => StaticBallCentered.source c R P (VectorFourier.coordinateMap y) j)
    (StaticBallDipole.source_integrable c R P j) hs
  rw [StaticBallDipole.source_moment c R P j, hm] at he
  exact he

end OQ14.SphereReactionDipole

#print axioms OQ14.SphereReactionDipole.integrand_integrable
#print axioms OQ14.SphereReactionDipole.integral_bound
#print axioms OQ14.SphereReactionDipole.integral_difference_bound
#print axioms OQ14.SphereReactionDipole.moment_error
#print axioms OQ14.SphereReactionDipole.ball_source_error

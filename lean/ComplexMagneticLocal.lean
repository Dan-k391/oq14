import ComplexExteriorIntegral
import MagneticLocal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticLocal
open Complex MeasureTheory Metric Filter OQ14.Maxwell OQ14.ComplexGreenKernel
open OQ14.WeakCurl (next previous)
open scoped Topology

theorem gradient_measurable (z : ℂ) (j : Fin 3) : Measurable (fun x : Space => phiGradient z x j) := by
  unfold phiGradient radialD
  fun_prop

theorem gradient_bound_ball (z : ℂ) (R : ℝ) (x : Space)
    (hxR : x ∈ closedBall 0 R) (j : Fin 3) :
    ‖phiGradient z x j‖ ≤ (4 * Real.pi)⁻¹ * Real.exp (‖z‖*R) *
      (‖z‖ * ‖x‖⁻¹ + (‖x‖⁻¹)^2) := by
  by_cases hx : x = 0
  · subst x
    simp [phiGradient, radialD]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hxR
  have hu : ‖((x j / ‖x‖ : ℝ) : ℂ)‖ ≤ 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm]
    exact (div_le_one hr).mpr (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
  have he : ‖Complex.exp (I*z*‖x‖)‖ ≤ Real.exp (‖z‖*R) := by
    apply (ComplexDynamicKernel.exp_norm_bound _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact mul_le_mul_of_nonneg_left hxnorm (norm_nonneg z)
  have hd : ‖radialD z ‖x‖‖ ≤ Real.exp (‖z‖*R) *
      (‖z‖ * ‖x‖⁻¹ + (‖x‖⁻¹)^2) := by
    unfold radialD
    rw [norm_mul]
    apply mul_le_mul he _ (norm_nonneg _) (Real.exp_pos _).le
    have h := norm_sub_le (I*z / (‖x‖ : ℂ)) (1 / (‖x‖ : ℂ)^2)
    simpa only [norm_div, norm_mul, norm_pow, norm_I, one_mul, norm_one,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, one_div, inv_pow,
      div_eq_mul_inv, norm_inv] using h
  have hm := mul_le_mul hd hu (norm_nonneg _) (by positivity)
  have hp : 0 < 4 * Real.pi := by positivity
  unfold phiGradient
  rw [norm_div, norm_mul]
  have hpi : ‖(4 * Real.pi : ℂ)‖ = 4 * Real.pi := by simp [norm_mul, Real.pi_pos.le]
  rw [hpi]
  calc
    _ ≤ (Real.exp (‖z‖*R) * (‖z‖ * ‖x‖⁻¹ + (‖x‖⁻¹)^2)) / (4 * Real.pi) :=
      div_le_div_of_nonneg_right (by simpa only [mul_one] using hm) hp.le
    _ = _ := by ring

theorem gradient_integrable_ball (z : ℂ) (R : ℝ) (j : Fin 3) :
    IntegrableOn (fun x : Space => phiGradient z x j) (closedBall 0 R) := by
  have h := ((KernelIntegrability.inverse_norm_integrable_ball R).const_mul ‖z‖).add
    (KernelIntegrability.inverse_norm_sq_integrable_ball R)
  apply (h.const_mul ((4 * Real.pi)⁻¹ * Real.exp (‖z‖*R))).mono'
    ((gradient_measurable z j).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact gradient_bound_ball z R x hx j

theorem gradient_locallyIntegrable (z : ℂ) (j : Fin 3) :
    LocallyIntegrable (fun x : Space => phiGradient z x j) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (gradient_integrable_ball z (max R 0) j).mono_set
    (hR.trans (closedBall_subset_closedBall (le_max_left _ _)))

def magnetic (z : ℂ) (ρ : Fin 3 → Space → ℂ) : Field := fun x i =>
  -(I*z) * (KernelConvolution.response (fun y => phiGradient z y (next i)) (ρ (previous i)) x -
    KernelConvolution.response (fun y => phiGradient z y (previous i)) (ρ (next i)) x)

theorem magnetic_memLp_ball (z : ℂ) (R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) : MemLp (fun x => magnetic z ρ x i) 2 (volume.restrict (closedBall 0 R)) := by
  have h1 := LocalConvolution.response_memLp_ball (fun y => phiGradient z y (next i))
    (gradient_locallyIntegrable z (next i)) (ρ (previous i)) (hρ (previous i))
    (NewtonL2.physicalCoordinate F (previous i)) (hF (previous i)) R S (hc (previous i))
  have h2 := LocalConvolution.response_memLp_ball (fun y => phiGradient z y (previous i))
    (gradient_locallyIntegrable z (previous i)) (ρ (next i)) (hρ (next i))
    (NewtonL2.physicalCoordinate F (next i)) (hF (next i)) R S (hc (next i))
  exact (h1.sub h2).const_mul (-(I*z))

theorem magnetic_locallyIntegrable (z : ℂ) (S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) : LocallyIntegrable (fun x => magnetic z ρ x i) := by
  have hh (j l : Fin 3) := LocalConvolution.response_locallyIntegrable
    (fun y => phiGradient z y j) (gradient_locallyIntegrable z j)
    (ρ l) (hρ l) (NewtonL2.physicalCoordinate F l) (hF l) S (hc l)
  exact ((hh (next i) (previous i)).sub (hh (previous i) (next i))).smul (-(I*z))

#print axioms OQ14.ComplexMagneticLocal.magnetic_locallyIntegrable
#print axioms OQ14.ComplexMagneticLocal.gradient_integrable_ball
#print axioms OQ14.ComplexMagneticLocal.gradient_locallyIntegrable
#print axioms OQ14.ComplexMagneticLocal.magnetic_memLp_ball
end OQ14.ComplexMagneticLocal




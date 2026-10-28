import ModalAxialKernel
import ComplexDynamicKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OQ14.ModalAxialComplexKernel
open Complex OQ14.Maxwell OQ14.ModalAxialRotation

theorem remainder_cov (θ : ℝ) (k : ℂ) (x : Space) (i l : Fin 3) :
    (∑ j : Fin 3, matrix θ i j * ComplexDynamicKernel.remainder k x j l) =
      ∑ j : Fin 3, ComplexDynamicKernel.remainder k (rotation θ x) i j * matrix θ j l := by
  simp only [ComplexDynamicKernel.remainder, ComplexDynamicKernel.dyadic, ComplexGreenKernel.phiHessian, ComplexGreenKernel.phi,
    (rotation θ).norm_map]
  fin_cases i <;> fin_cases l <;>
    simp [matrix, Fin.sum_univ_three, rotation, spatial, WithLp.equiv_symm_pi_apply,
      ofReal_add, ofReal_sub, ofReal_mul]
  all_goals simp only [div_eq_mul_inv]
  all_goals ring_nf
  all_goals
    have h : (Complex.cos (θ : ℂ))^2 = 1 - (Complex.sin (θ : ℂ))^2 := by
      have h' := Real.cos_sq_add_sin_sq θ
      have hc : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by exact_mod_cast h'
      simpa only [ofReal_cos, ofReal_sin] using (eq_sub_of_add_eq hc)
    have h3 : (Complex.cos (θ : ℂ))^3 = Complex.cos (θ : ℂ) * (1 - (Complex.sin (θ : ℂ))^2) := by
      calc _ = Complex.cos (θ : ℂ) * (Complex.cos (θ : ℂ))^2 := by ring
        _ = _ := by rw [h]
    simp only [h3, h]
    ring

#print axioms OQ14.ModalAxialComplexKernel.remainder_cov
end OQ14.ModalAxialComplexKernel






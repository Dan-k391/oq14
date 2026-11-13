import Packet06ComplexScalarPotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderTransfer
open MeasureTheory Metric OQ14.Maxwell OQ14.Packet06ComplexScalarPotential

/-- A quantitative L² translation modulus transfers to the actual compact-source Green
convolution and its physical z² factor, with no change of representative. -/
theorem response_difference_of_row_bound (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : ScalarL2) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (x y : Space) (hx : x ∈ closedBall 0 R) (hy : y ∈ closedBall 0 R)
    (C : ℝ)
    (hm : dist (L2KernelCompact.row (cutoff z (R+S)) x)
        (L2KernelCompact.row (cutoff z (R+S)) y) ≤ C * Real.sqrt (dist x y)) :
    dist (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ x)
      (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ y) ≤
      ‖z‖^2 * ‖F‖ * C * Real.sqrt (dist x y) := by
  rw [← value_eq_response z R S ρ F hF hc x hx,
    ← value_eq_response z R S ρ F hF hc y hy]
  rw [dist_eq_norm, ← mul_sub, norm_mul, norm_pow]
  have h := L2KernelCompact.value_difference_le (cutoff z (R+S)) F x y
  rw [dist_eq_norm] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg F))
  calc
    ‖z‖ ^ 2 * ‖L2KernelCompact.value (cutoff z (R+S)) F x -
        L2KernelCompact.value (cutoff z (R+S)) F y‖ ≤
        ‖z‖ ^ 2 * (‖F‖ * (C * Real.sqrt (dist x y))) :=
          mul_le_mul_of_nonneg_left h' (sq_nonneg ‖z‖)
    _ = _ := by ring

#print axioms OQ14.Packet06GreenHolderTransfer.response_difference_of_row_bound
end OQ14.Packet06GreenHolderTransfer

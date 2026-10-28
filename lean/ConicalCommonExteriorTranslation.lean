import ConicalCommonAngular

/-! Translation covariance of the literal exterior integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalCommonExteriorTranslation
open MeasureTheory OQ14.Maxwell
abbrev Space := Maxwell.Space

theorem response_translate (q ρ : Space → ℂ) (c x : Space) :
    KernelConvolution.response q (fun y => ρ (y-c)) (x+c) = KernelConvolution.response q ρ x := by
  unfold KernelConvolution.response
  have h := integral_add_right_eq_self (μ := (volume : Measure Space))
    (fun y => ρ (y-c) * q (x+c-y)) c
  simpa only [add_sub_cancel_right, add_sub_add_right_eq_sub] using h.symm

theorem electric_translate (k : ℝ) (ρ : Fin 3 → Space → ℂ) (c x : Space) (i : Fin 3) :
    ExteriorContinuity.electric k (fun j y => ρ j (y-c)) (x+c) i =
      ExteriorContinuity.electric k ρ x i := by
  simp only [ExteriorContinuity.electric, response_translate]

end OQ14.ConicalCommonExteriorTranslation
#print axioms OQ14.ConicalCommonExteriorTranslation.response_translate
#print axioms OQ14.ConicalCommonExteriorTranslation.electric_translate

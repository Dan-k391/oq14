import Packet07DrivenUniformFixedTarget

/-! An explicit positive binary contrast below any prescribed material ceiling. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformMaterialCeiling

theorem positive_contrast_below (epsilonMax : ℝ) (h : 1 < epsilonMax) :
    ∃ d : ℝ, 0 < d ∧ 1+d ≤ epsilonMax := by
  exact ⟨(epsilonMax-1)/2,by linarith,by linarith⟩
end OQ14.Packet07DrivenUniformMaterialCeiling
#print axioms OQ14.Packet07DrivenUniformMaterialCeiling.positive_contrast_below

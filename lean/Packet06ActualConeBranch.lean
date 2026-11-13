import Packet06ModalConeBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ActualConeBranch
open Set Metric OQ14.Maxwell
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [DecidableEq ι] in
theorem local_dielectric_match (n : ℝ) (hn : 1 < n) (i : ι)
    (hcontrast_i : (p i).contrast = n^2) (η : ℝ) (hη : 0 ≤ η)
    (x : Space) (hx : ‖x-center i‖ ≤ a i) (hsphere : ‖x‖ < 1) :
    1 + (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn)
      (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) η hη).value
      (VectorFourier.coordinateMap x) = n^2 * ConicalCapField.permittivity η (p i).threshold (x-center i) := by
  apply Packet06ModalConeBranch.local_dielectric_match n hn (p i) (a i) η hη hcontrast_i (ha i)
    _ (center i) x hx hsphere
  apply ConicalCommonMaterial.coefficient_local p a center B hB hcontrast ha hsep i x
  change ‖x-center i‖ ≤ (p i).cutoff.rOut
  exact hx.trans (ha i)
#print axioms OQ14.Packet06ActualConeBranch.local_dielectric_match
end OQ14.Packet06ActualConeBranch

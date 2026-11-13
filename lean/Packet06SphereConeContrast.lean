import Packet06SphereInsertionMode
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SphereConeContrast
open Set Metric OQ14.Maxwell
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i)

omit [DecidableEq ι] in
theorem inserted_value (n : ℝ) (hn : 1 < n) (hcontrast_eq : ∀ i, (p i).contrast = n^2)
    (j : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (x : Space) :
    (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn)
      (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j) η hη).value
      (VectorFourier.coordinateMap x) =
      (ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) +
        (by classical exact if x ∈ CommonBinaryInterface.body p a center j then η * n^2 else 0) := by
  classical
  change (ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) +
    η * (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j).value
      (VectorFourier.coordinateMap x) = _
  rw [CommonBinaryInterface.coefficient_body p a center B hB hcontrast ha0 ha hsep (n^2) hcontrast_eq]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem inside_material (n : ℝ) (hn : 1 < n) (hcontrast_eq : ∀ i, (p i).contrast = n^2)
    (j : ℕ) (hinside : CommonBinaryInterface.body p a center j ⊆ ball (0 : Space) 1)
    (η : ℝ) (hη : 0 ≤ η) (x : Space) (hx : x ∈ CommonBinaryInterface.body p a center j) :
    1 + (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn)
      (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j) η hη).value
      (VectorFourier.coordinateMap x) = (1+η)*n^2 := by
  rw [inserted_value p a center B hB hcontrast ha hsep ha0 n hn hcontrast_eq j η hη x,
    if_pos hx,ModalWeightedMode.coefficient_value]
  have hxball : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hinside hx
  rw [if_pos hxball]
  ring
#print axioms OQ14.Packet06SphereConeContrast.inserted_value
#print axioms OQ14.Packet06SphereConeContrast.inside_material
end OQ14.Packet06SphereConeContrast

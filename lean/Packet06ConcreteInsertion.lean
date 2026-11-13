import Packet06ShrinkingInsertion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConcreteInsertion
open Set Metric OQ14.Maxwell Packet06MaterialSymmetry Packet06MaterialInsertion
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i)

omit [DecidableEq ι] in
theorem rounded_support_small (r : ℝ) (har : ∀ i, a i ≤ r) (n : ℕ) (x : Space)
    (hx : ∀ i, r < dist x (center i)) :
    (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value
      (VectorFourier.coordinateMap x) = 0 := by
  classical
  simp only [CommonBinaryRounding.coefficient,MeasurableEquiv.symm_apply_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hdist : a i < ‖x-center i‖ := by
    have h := hx i
    rw [dist_eq_norm] at h
    exact (har i).trans_lt h
  have hnot : x-center i ∉ ConicalJunctionPhysical.inclusion n
      (ConicalJunctionPhysical.slope (p i).threshold) (a i) := by
    intro hm
    have hi := ConicalJunctionPhysical.inclusion_norm_bound n _ _ (ha0 i) (x-center i) hm
    linarith
  simp [CommonBinaryRounding.localValue,ConicalJunctionPhysical.binaryMaterial,hnot]

omit [DecidableEq ι] in
theorem sphere_plus_rounded_axial (n : ℝ) (hn : 1 < n)
    (hc : Packet06ConeUnionSymmetry.OnAxis center) (j : ℕ) :
    Axial (unionCoefficient (ModalWeightedMode.coefficient n hn)
      (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j)) :=
  union_axial _ _ (Packet06SphereSymmetry.sphere_axial n hn)
    (Packet06ConeUnionSymmetry.rounded_axial p a center B hB hcontrast ha hsep ha0 hc j)

omit [DecidableEq ι] in
theorem sphere_plus_rounded_meridional (n : ℝ) (hn : 1 < n)
    (hc : Packet06ConeUnionSymmetry.OnAxis center) (j : ℕ) :
    Meridional (unionCoefficient (ModalWeightedMode.coefficient n hn)
      (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j)) :=
  union_meridional _ _ (Packet06SphereSymmetry.sphere_meridional n hn)
    (Packet06ConeUnionSymmetry.rounded_meridional p a center B hB hcontrast ha hsep ha0 hc j)
#print axioms OQ14.Packet06ConcreteInsertion.rounded_support_small
#print axioms OQ14.Packet06ConcreteInsertion.sphere_plus_rounded_axial
#print axioms OQ14.Packet06ConcreteInsertion.sphere_plus_rounded_meridional
end OQ14.Packet06ConcreteInsertion

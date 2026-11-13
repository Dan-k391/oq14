import Packet06SphereSymmetry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeUnionSymmetry
open Set Metric OQ14.Maxwell Packet06MaterialSymmetry Packet06ConeSymmetry
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def OnAxis (center : ι → Space) : Prop := ∀ i, center i 0 = 0 ∧ center i 1 = 0

omit [Fintype ι] [DecidableEq ι] in
theorem rotation_center (center : ι → Space) (hc : OnAxis center) (θ : ℝ) (i : ι) :
    ModalAxialRotation.rotation θ (center i) = center i := by
  ext j
  fin_cases j <;> simp [ModalAxialRotation.rotation,ModalAxialRotation.spatial,
    WithLp.equiv_symm_pi_apply,(hc i).1,(hc i).2]

omit [Fintype ι] [DecidableEq ι] in
theorem reflection_center (center : ι → Space) (hc : OnAxis center) (i : ι) :
    ModalMeridionalReflection.reflection (center i) = center i := by
  ext j
  rw [ModalMeridionalReflection.reflection_coordinate]
  fin_cases j <;> simp [ModalMeridionalReflection.sign,(hc i).1,(hc i).2]

omit [Fintype ι] [DecidableEq ι] in
theorem rotation_norm_axis (center : ι → Space) (hc : OnAxis center) (θ : ℝ) (i : ι) (x : Space) :
    ‖ModalAxialRotation.rotation θ x - center i‖ = ‖x-center i‖ ∧
      (ModalAxialRotation.rotation θ x-center i) 2 = (x-center i) 2 := by
  have he : ModalAxialRotation.rotation θ x - center i = ModalAxialRotation.rotation θ (x-center i) := by
    rw [map_sub,rotation_center center hc θ i]
  rw [he,(ModalAxialRotation.rotation θ).norm_map]
  constructor
  · rfl
  · simp [ModalAxialRotation.rotation,ModalAxialRotation.spatial,WithLp.equiv_symm_pi_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem reflection_norm_axis (center : ι → Space) (hc : OnAxis center) (i : ι) (x : Space) :
    ‖ModalMeridionalReflection.reflection x-center i‖ = ‖x-center i‖ ∧
      (ModalMeridionalReflection.reflection x-center i) 2 = (x-center i) 2 := by
  have he : ModalMeridionalReflection.reflection x-center i = ModalMeridionalReflection.reflection (x-center i) := by
    rw [map_sub,reflection_center center hc i]
  rw [he,ModalMeridionalReflection.reflection.norm_map]
  constructor
  · rfl
  · simp [ModalMeridionalReflection.reflection_coordinate,ModalMeridionalReflection.sign]

variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i)

omit [DecidableEq ι] in
theorem literal_axial (hc : OnAxis center) : Axial (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) := by
  intro θ x
  rw [ConicalCommonMaterial.coefficient_spatial,ConicalCommonMaterial.coefficient_spatial]
  apply Finset.sum_congr rfl
  intro i _
  exact literal_material_invariant (p i) (a i) (rotation_norm_axis center hc θ i x).1 (rotation_norm_axis center hc θ i x).2

omit [DecidableEq ι] in
theorem literal_meridional (hc : OnAxis center) : Meridional (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) := by
  intro x
  rw [ConicalCommonMaterial.coefficient_spatial,ConicalCommonMaterial.coefficient_spatial]
  apply Finset.sum_congr rfl
  intro i _
  exact literal_material_invariant (p i) (a i) (reflection_norm_axis center hc i x).1 (reflection_norm_axis center hc i x).2

omit [DecidableEq ι] in
theorem rounded_axial (hc : OnAxis center) (n : ℕ) : Axial (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n) := by
  intro θ x
  simp only [CommonBinaryRounding.coefficient,MeasurableEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact binary_material_invariant (p i) (a i) n (rotation_norm_axis center hc θ i x).1 (rotation_norm_axis center hc θ i x).2

omit [DecidableEq ι] in
theorem rounded_meridional (hc : OnAxis center) (n : ℕ) : Meridional (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n) := by
  intro x
  simp only [CommonBinaryRounding.coefficient,MeasurableEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact binary_material_invariant (p i) (a i) n (reflection_norm_axis center hc i x).1 (reflection_norm_axis center hc i x).2
#print axioms OQ14.Packet06ConeUnionSymmetry.rotation_center
#print axioms OQ14.Packet06ConeUnionSymmetry.reflection_center
#print axioms OQ14.Packet06ConeUnionSymmetry.rotation_norm_axis
#print axioms OQ14.Packet06ConeUnionSymmetry.reflection_norm_axis
#print axioms OQ14.Packet06ConeUnionSymmetry.literal_axial
#print axioms OQ14.Packet06ConeUnionSymmetry.literal_meridional
#print axioms OQ14.Packet06ConeUnionSymmetry.rounded_axial
#print axioms OQ14.Packet06ConeUnionSymmetry.rounded_meridional
end OQ14.Packet06ConeUnionSymmetry

import CommonBinaryCollar

/-! The common rounded susceptibility has exactly the two prescribed values. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.CommonBinaryValues
open Set Metric
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))
  (ha0 : ∀ i, 0 < a i)

omit [DecidableEq ι] in
theorem two_values (d : ℝ) (hd : ∀ i, (p i).contrast = d) (n : ℕ) (ξ : StaticCoefficient.Space) :
    (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value ξ = 0 ∨
    (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value ξ = d := by
  classical
  let x := VectorFourier.coordinateMap.symm ξ
  by_cases hex : ∃ i, x ∈ ConicalCommonMaterial.outer p center i
  · obtain ⟨i,hi⟩ := hex
    have hl := CommonBinaryCollar.common_local p a center B hB hcontrast ha hsep ha0 n i x hi
    have hξ : VectorFourier.coordinateMap x = ξ := MeasurableEquiv.apply_symm_apply _ ξ
    rw [hξ] at hl
    rw [hl]
    simp only [CommonBinaryRounding.localValue, ConicalJunctionPhysical.binaryMaterial]
    split_ifs with h
    · exact Or.inr (hd i)
    · exact Or.inl rfl
  · have hz : (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value ξ = 0 := by
      change (∑ i, ConicalCommonMaterial.localValue p a center i x) = 0
      apply Finset.sum_eq_zero
      intro i _
      apply ConicalCommonMaterial.localValue_zero
      intro hi
      exact hex ⟨i, ConicalCommonMaterial.material_subset_outer p a center ha i hi⟩
    have hb := CommonBinaryRounding.coefficient_below p a center B hB hcontrast ha hsep ha0 n ξ
    have hn := (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).nonnegative ξ
    left
    linarith

end OQ14.CommonBinaryValues
#print axioms OQ14.CommonBinaryValues.two_values

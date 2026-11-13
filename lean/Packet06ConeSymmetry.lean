import Packet06SymmetryPencil
import CommonBinaryRounding
import CommonBinaryInterface
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeSymmetry
open Set Metric OQ14.Maxwell
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data

theorem horizontal_norm_of_norm_axis {x y : Space} (hn : ‖x‖ = ‖y‖) (hz : x 2 = y 2) :
    ‖ConicalJunctionPhysical.horizontal x‖ = ‖ConicalJunctionPhysical.horizontal y‖ := by
  have hx := ConicalJunctionPhysical.norm_sq_split x
  have hy := ConicalJunctionPhysical.norm_sq_split y
  rw [hn,hz] at hx
  nlinarith [norm_nonneg (ConicalJunctionPhysical.horizontal x),
    norm_nonneg (ConicalJunctionPhysical.horizontal y)]

theorem rounded_inclusion_invariant (n : ℕ) (m a : ℝ) {x y : Space}
    (hn : ‖x‖ = ‖y‖) (hz : x 2 = y 2) :
    x ∈ ConicalJunctionPhysical.inclusion n m a ↔ y ∈ ConicalJunctionPhysical.inclusion n m a := by
  have hh := horizontal_norm_of_norm_axis hn hz
  simp only [ConicalJunctionPhysical.inclusion,mem_preimage,ConicalSmoothJunction.inclusion,mem_setOf_eq,
    ConicalSmoothJunction.coneMargin,ConicalSmoothJunction.ballMargin,ConicalJunctionPhysical.split,
    ConicalSmoothCapGraph.cap]
  rw [hh,hz]

theorem literal_material_invariant (p : Data) (a : ℝ) {x y : Space}
    (hn : ‖x‖ = ‖y‖) (hz : x 2 = y 2) :
    (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) =
      (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap y) := by
  classical
  simp only [ConicalSeparatedSource.material,MeasurableEquiv.symm_apply_apply]
  rw [hn]
  split_ifs with h
  · rw [ConicalStaticVolume.coefficient_spatial,ConicalStaticVolume.coefficient_spatial]
    unfold ConicalAnnularSource.dielectric
    have hball : x ∈ closedBall (0 : Space) p.cutoff.rOut ↔ y ∈ closedBall (0 : Space) p.cutoff.rOut := by
      simp only [mem_closedBall,dist_zero_right,hn]
    rw [hball]
    split_ifs
    · unfold ConicalCapField.permittivity
      congr 1
      unfold ConicalCapField.unit
      by_cases hx : x = 0
      · have hy : y = 0 := norm_eq_zero.mp (hn ▸ (norm_eq_zero.mpr hx))
        simp [hx,hy]
      · have hy : y ≠ 0 := by
          intro hy
          have : ‖x‖ = 0 := hn.trans (norm_eq_zero.mpr hy)
          exact hx (norm_eq_zero.mp this)
        simp [hx,hy,hn,hz]
    · rfl
  · rfl

theorem binary_material_invariant (p : Data) (a : ℝ) (n : ℕ) {x y : Space}
    (hn : ‖x‖ = ‖y‖) (hz : x 2 = y 2) :
    (ConicalJunctionPhysical.binaryMaterial p a n).value (VectorFourier.coordinateMap x) =
      (ConicalJunctionPhysical.binaryMaterial p a n).value (VectorFourier.coordinateMap y) := by
  classical
  simp only [ConicalJunctionPhysical.binaryMaterial,MeasurableEquiv.symm_apply_apply]
  rw [rounded_inclusion_invariant n _ _ hn hz]
#print axioms OQ14.Packet06ConeSymmetry.horizontal_norm_of_norm_axis
#print axioms OQ14.Packet06ConeSymmetry.rounded_inclusion_invariant
#print axioms OQ14.Packet06ConeSymmetry.literal_material_invariant
#print axioms OQ14.Packet06ConeSymmetry.binary_material_invariant
end OQ14.Packet06ConeSymmetry

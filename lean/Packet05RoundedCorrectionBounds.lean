import Packet05UniformMaterialCorrection
import Packet06RoundedPeakFamily

/-! Every convergent rounded mode family has a common original-source
envelope and hence genuine uniform compact H2 and pointwise Green bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RoundedCorrectionBounds
open MeasureTheory Set Metric Filter Maxwell WeakCurl WeakPoynting DivCurlCompact
  Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem rounded_family_envelope {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z₀ : ℂ) (v₀ : Packet06SectorOperator.Sector)
    (hz : Tendsto z atTop (𝓝 z₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    ∃ Z L B : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧ 0 ≤ B ∧
      (∀ j, ‖z j‖ ≤ Z) ∧ (∀ j, ‖(v j : VectorFourier.VectorL2)‖ ≤ L) ∧
      ∀ j, (rounded n hn g η hη j).bound ≤ B := by
  obtain ⟨Z,hZ,hzB⟩ := (Metric.isBounded_range_of_tendsto z hz).exists_pos_norm_le
  obtain ⟨L,hL,hvB⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_pos_norm_le
  let B := (ModalWeightedMode.coefficient n hn).bound+η*n^2
  have hB : 0 ≤ B := StaticCoefficient.bound_nonnegative (rounded n hn g η hη 0)
  exact ⟨Z,L,B,hZ.le,hL.le,hB,fun j => hzB _ (mem_range_self j),
    fun j => hvB _ (mem_range_self j),fun _ => le_rfl⟩

theorem rounded_family_correction {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z₀ : ℂ) (v₀ : Packet06SectorOperator.Sector)
    (hz : Tendsto z atTop (𝓝 z₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (R : ℝ) (hR : 0 ≤ R) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχR : tsupport χ.function ⊆ ball (0 : Space) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j k,
      ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial U (D i) i) ∧ (∀ i l, HasWeakPartial (D i) (T i l) l) ∧
        (∀ᵐ x ∂volume, U x=χ.function x*Packet06ComplexPotential.correction (z j)
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k) ∧
        ‖U‖ ≤ C ∧ (∀ i, ‖D i‖ ≤ C) ∧ (∀ i l, ‖T i l‖ ≤ C) ∧
        ∀ x, χ.function x=1 → ‖Packet06ComplexPotential.correction (z j)
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k‖ ≤
          10*Packet05ExplicitAnisotropicBound.universalConstant*C := by
  obtain ⟨Z,L,B,hZ,hL,_,hzB,hvB,hB⟩ := rounded_family_envelope n hn g η hη z v z₀ v₀ hz hv
  exact Packet05UniformMaterialCorrection.material_family_correction (rounded n hn g η hη) z
    (fun j => (v j : VectorFourier.VectorL2)) R 1 Z B L hR (by norm_num) hZ hL
    (Packet05RoundedModeSupport.rounded_support n hn g η hη) hB hzB hvB χ hχ2 hχR

end OQ14.Packet05RoundedCorrectionBounds
#print axioms OQ14.Packet05RoundedCorrectionBounds.rounded_family_envelope
#print axioms OQ14.Packet05RoundedCorrectionBounds.rounded_family_correction

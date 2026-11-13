import Packet05ActualCorrectionH2
import Packet06MaxwellScalarEquation

/-! The actual material-source correction of a complex-frequency mode has
compact H² cutoffs; all source assumptions follow from the mode coefficient. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ModeCorrectionH2
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05ActualCorrectionH2

theorem mode_correction_compact_h2 (c : StaticCoefficient.Coefficient) (z : ℂ)
    (S R : ℝ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R)
    (k : Fin 3) :
    ∃ U : L2Scalar, ∃ G : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ j, HasWeakPartial U (G j) j) ∧
      (∀ i j, HasWeakPartial (G i) (H i j) j) ∧
      (∀ᵐ x ∂volume, U x = χ.function x *
        Packet06ComplexPotential.correction z (DynamicVolume.source c u) x k) :=
  correction_component_compact_h2 z R S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (MaterialField.source_compact c u S hc) (DynamicVolume.source_zero c u S hc)
    (StaticNewton.material_source_ae c u) χ hχ2 hχR k

end OQ14.Packet05ModeCorrectionH2
#print axioms OQ14.Packet05ModeCorrectionH2.mode_correction_compact_h2

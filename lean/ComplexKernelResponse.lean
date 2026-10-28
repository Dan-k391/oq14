import ComplexConvolutionAnalytic
import ModalWeightedMode
import HomogeneousVolumeUniqueness

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexKernelResponse
open MeasureTheory Metric OQ14.Maxwell
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def response (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2) : VectorL2 :=
  NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u) +
    ComplexConvolutionAnalytic.operator z (2*R) (StaticCoefficient.sqrtMultiplier c u)

theorem kernel_weighted_response (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    u = StaticCoefficient.sqrtMultiplier c (response c z R u) := by
  change (u - StaticCoefficient.sqrtMultiplier c
    (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u))) -
      StaticCoefficient.sqrtMultiplier c
        (ComplexConvolutionAnalytic.operator z (2*R) (StaticCoefficient.sqrtMultiplier c u)) = 0 at hker
  simp only [response, map_add]
  have h := sub_eq_zero.mp hker
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem kernel_coordinate_ae (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    (fun x : Space => u (VectorFourier.coordinateMap x)) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) •
        response c z R u (VectorFourier.coordinateMap x) := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (response c z R u))
  simpa only [← kernel_weighted_response c z R u hker] using h

theorem kernel_zero_outside (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R u = 0)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 R → u (VectorFourier.coordinateMap x) = 0 := by
  filter_upwards [kernel_coordinate_ae c z R u hker] with x hx hxo
  rw [hx, hc x hxo]
  simp

#print axioms OQ14.ComplexKernelResponse.kernel_weighted_response
#print axioms OQ14.ComplexKernelResponse.kernel_coordinate_ae
#print axioms OQ14.ComplexKernelResponse.kernel_zero_outside
end OQ14.ComplexKernelResponse





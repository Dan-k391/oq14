import Packet06GreenHolderEndpoint
import DynamicVolume
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderMaterial
open MeasureTheory Metric OQ14.Maxwell OQ14.Packet06GreenHolderEndpoint

/-- Uniform local Hölder control for the literal dynamic-volume material source. -/
theorem material_response_holder (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (j : Fin 3) (z : ℂ) (Z R S : ℝ) (hZ : ‖z‖ ≤ Z)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ y : Space, y ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap y) = 0)
    (x x' : Space) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hsmall : ‖x-x'‖ ≤ 1) :
    dist (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) (DynamicVolume.source c u j) x)
      (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) (DynamicVolume.source c u j) x') ≤
      Z^2 * ‖NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) j‖ *
        Packet06GreenHolderEndpoint.constant Z R S * Real.sqrt (dist x x') := by
  apply actual_response_holder z Z R S hZ hR hS (DynamicVolume.source c u j)
    (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) j)
    (StaticNewton.material_source_ae c u j)
  · exact DynamicVolume.source_zero c u S hc j
  · exact hx
  · exact hx'
  · exact hsmall

#print axioms OQ14.Packet06GreenHolderMaterial.material_response_holder
end OQ14.Packet06GreenHolderMaterial

import Packet05ActualOrientedModeScalar
import Packet05ChartOrientation
import Packet05LocalDerivative

/-! Binary material equality on a graph chart holds almost everywhere; the
flat plane is null and needs no boundary-value convention. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartBinaryMatch
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalJunctionPhysical
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05ChartBasis
  OQ14.Packet05FlatWeight OQ14.Packet05LocalDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem chart_binary_match_ae (c : StaticCoefficient.Coefficient) (B : Set Maxwell.Space) (d : ℝ)
    (hbin : ∀ y : Maxwell.Space, c.value (VectorFourier.coordinateMap y) = (by classical exact if y ∈ B then d else 0))
    (up : Bool) (i : Fin 3) (g : Plane → ℝ) (W : Set Maxwell.Space)
    (hside : ∀ x ∈ W, inverseOriented up i (graphMap (liftedHeight g) x) ∈ B ↔ 0 < x 2) :
    ∀ᵐ x ∂volume, x ∈ W →
      Packet06MaxwellScalarEquation.epsilon c (inverseOriented up i (graphMap (liftedHeight g) x)) = weight d x := by
  classical
  have hn : ∀ᵐ x : Maxwell.Space ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  filter_upwards [hn] with x hx hW
  have hside' := hside x hW
  by_cases hneg : x 2 < 0
  · have hnot : inverseOriented up i (graphMap (liftedHeight g) x) ∉ B := by
      intro h
      have := hside'.mp h
      linarith
    simp [Packet06MaxwellScalarEquation.epsilon,hbin,weight,FlatDifferenceCoercivity.dielectric,hneg,hnot]
  · have hpos : 0 < x 2 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    have hin := hside'.mpr hpos
    simp [Packet06MaxwellScalarEquation.epsilon,hbin,weight,FlatDifferenceCoercivity.dielectric,hneg,hin]

end OQ14.Packet05ChartBinaryMatch
#print axioms OQ14.Packet05ChartBinaryMatch.chart_binary_match_ae

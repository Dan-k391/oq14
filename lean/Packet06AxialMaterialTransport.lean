import Packet06MaterialSymmetry
import Packet06AxialSource

/-! Arbitrary material transported by a continuous proper axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialMaterialTransport
open Complex MeasureTheory Maxwell StaticCoefficient ModalAxialRotation

def coefficient (θ : ℝ) (c : Coefficient) : Coefficient where
  value := fun ξ => c.value (VectorFourier.coordinateMap (rotation (-θ) (VectorFourier.coordinateMap.symm ξ)))
  bound := c.bound
  measurable := c.measurable.comp (VectorFourier.coordinateMap.measurable.comp
    ((rotation (-θ)).continuous.measurable.comp VectorFourier.coordinateMap.symm.measurable))
  nonnegative := fun _ => c.nonnegative _
  bounded := fun _ => c.bounded _

theorem coefficient_value (θ : ℝ) (c : Coefficient) (x : Maxwell.Space) :
    (coefficient θ c).value (VectorFourier.coordinateMap x) =
      c.value (VectorFourier.coordinateMap (rotation (-θ) x)) := by simp [coefficient]

theorem dielectric_value (θ : ℝ) (c : Coefficient) (x : Maxwell.Space) :
    MaterialMaxwell.dielectric (coefficient θ c) x =
      MaterialMaxwell.dielectric c (rotation (-θ) x) := by
  simp [MaterialMaxwell.dielectric,coefficient_value]

theorem sqrt_transport (θ : ℝ) (c : Coefficient) (F : VectorFourier.VectorL2) :
    action θ (sqrtMultiplier c F) = sqrtMultiplier (coefficient θ c) (action θ F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (sqrtMultiplier_ae c F)
  have hs' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (sqrtMultiplier_ae (coefficient θ c) (action θ F))
  have hr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae hs
  filter_upwards [action_ae θ (sqrtMultiplier c F) i, hr, hs', action_ae θ F i] with x h1 h2 h3 h4
  rw [h1,h3]
  simp only [PiLp.smul_apply,smul_eq_mul]
  rw [h4]
  simp_rw [h2]
  simp only [PiLp.smul_apply,smul_eq_mul]
  rw [coefficient_value,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem source_transport (θ : ℝ) (c : Coefficient) (u : VectorFourier.VectorL2) (i : Fin 3) :
    DynamicVolume.source (coefficient θ c) (action θ u) i =ᵐ[volume]
      fun y => ∑ j : Fin 3, matrix θ i j * DynamicVolume.source c u j (rotation (-θ) y) := by
  filter_upwards [action_ae θ u i] with y hy
  unfold DynamicVolume.source
  rw [hy,coefficient_value,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem static_transport (θ : ℝ) (c : Coefficient) (F : VectorFourier.VectorL2) :
    action θ (weightedBlock c F) = weightedBlock (coefficient θ c) (action θ F) := by
  unfold weightedBlock
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply,map_add]
  rw [sqrt_transport,ModalAxialStatic.action_projection,sqrt_transport]

end OQ14.Packet06AxialMaterialTransport
#print axioms OQ14.Packet06AxialMaterialTransport.coefficient_value
#print axioms OQ14.Packet06AxialMaterialTransport.dielectric_value
#print axioms OQ14.Packet06AxialMaterialTransport.sqrt_transport
#print axioms OQ14.Packet06AxialMaterialTransport.source_transport
#print axioms OQ14.Packet06AxialMaterialTransport.static_transport

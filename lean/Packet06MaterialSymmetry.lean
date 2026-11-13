import ModalMeridionalStatic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialSymmetry
open Complex MeasureTheory OQ14.Maxwell OQ14.StaticCoefficient
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

def Axial (c : Coefficient) : Prop := ∀ (θ : ℝ) (x : Space),
  c.value (VectorFourier.coordinateMap (ModalAxialRotation.rotation θ x)) =
    c.value (VectorFourier.coordinateMap x)
def Meridional (c : Coefficient) : Prop := ∀ x : Space,
  c.value (VectorFourier.coordinateMap (ModalMeridionalReflection.reflection x)) =
    c.value (VectorFourier.coordinateMap x)

open ModalAxialRotation in
theorem axial_sqrt_comm (c : Coefficient) (hc : Axial c) (θ : ℝ) (F : V) :
    ModalAxialRotation.action θ (sqrtMultiplier c F) = sqrtMultiplier c (ModalAxialRotation.action θ F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (sqrtMultiplier_ae c F)
  have hs' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (sqrtMultiplier_ae c (action θ F))
  have hr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae hs
  filter_upwards [action_ae θ (sqrtMultiplier c F) i, hr, hs', action_ae θ F i] with x h1 h2 h3 h4
  rw [h1,h3]
  simp only [PiLp.smul_apply,smul_eq_mul]
  rw [h4]
  simp_rw [h2]
  simp only [PiLp.smul_apply,smul_eq_mul]
  rw [hc (-θ) x,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

open ModalMeridionalReflection ModalMeridionalStatic HalfTurnVectorAction in
theorem meridional_sqrt_comm (c : Coefficient) (hc : Meridional c) (F : V) :
    ModalMeridionalReflection.action (sqrtMultiplier c F) =
      sqrtMultiplier c (ModalMeridionalReflection.action F) := by
  apply vector_ext_pt
  intro i
  have ha : (fun y => DynamicVolume.source c (action F) i y) =ᵐ[volume]
      fun y => (sign i : ℂ) * DynamicVolume.source c F i (reflection y) := by
    filter_upwards [action_ae F i] with y hy
    unfold DynamicVolume.source
    rw [hy,hc y]
    ring
  filter_upwards [action_ae (sqrtMultiplier c F) i, ae_reflect (sqrt_pt c F i),
    sqrt_pt c (action F) i, ha] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

theorem axial_static_comm (c : Coefficient) (hc : Axial c) (θ : ℝ) (F : V) :
    ModalAxialRotation.action θ (weightedBlock c F) = weightedBlock c (ModalAxialRotation.action θ F) := by
  unfold weightedBlock
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply,map_add]
  rw [axial_sqrt_comm c hc,ModalAxialStatic.action_projection,axial_sqrt_comm c hc]

theorem meridional_static_comm (c : Coefficient) (hc : Meridional c) (F : V) :
    ModalMeridionalReflection.action (weightedBlock c F) = weightedBlock c (ModalMeridionalReflection.action F) := by
  unfold weightedBlock
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply,map_add]
  rw [meridional_sqrt_comm c hc,ModalMeridionalStatic.action_physicalProjection,meridional_sqrt_comm c hc]
#print axioms OQ14.Packet06MaterialSymmetry.axial_sqrt_comm
#print axioms OQ14.Packet06MaterialSymmetry.meridional_sqrt_comm
#print axioms OQ14.Packet06MaterialSymmetry.axial_static_comm
#print axioms OQ14.Packet06MaterialSymmetry.meridional_static_comm
end OQ14.Packet06MaterialSymmetry

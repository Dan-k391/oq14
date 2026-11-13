import Packet06CyclicL2

/-! Actual coefficient and square-root material multiplier under cyclic rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicMaterial
open MeasureTheory Packet06CyclicRotation Packet06CyclicL2

def coefficient (c : StaticCoefficient.Coefficient) : StaticCoefficient.Coefficient where
  value := fun ξ => c.value (VectorFourier.coordinateMap (unrotate (VectorFourier.coordinateMap.symm ξ)))
  bound := c.bound
  measurable := c.measurable.comp (VectorFourier.coordinateMap.measurable.comp
    (rotation.symm.continuous.measurable.comp VectorFourier.coordinateMap.symm.measurable))
  nonnegative := fun _ => c.nonnegative _
  bounded := fun _ => c.bounded _

theorem coefficient_value (c : StaticCoefficient.Coefficient) (x : Maxwell.Space) :
    (coefficient c).value (VectorFourier.coordinateMap x) =
      c.value (VectorFourier.coordinateMap (unrotate x)) := by
  simp [coefficient]

theorem dielectric_value (c : StaticCoefficient.Coefficient) (x : Maxwell.Space) :
    MaterialMaxwell.dielectric (coefficient c) x = MaterialMaxwell.dielectric c (unrotate x) := by
  simp [MaterialMaxwell.dielectric, coefficient_value]

theorem multiplier_action (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) :
    StaticCoefficient.sqrtMultiplier (coefficient c) (action u) =
      action (StaticCoefficient.sqrtMultiplier c u) := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have ha := action_ae (StaticCoefficient.sqrtMultiplier c u) i
  have hu := action_ae u i
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient c) (action u))
  have hn0 := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c u)
  have hn := rotation.symm.measurePreserving.quasiMeasurePreserving.ae hn0
  filter_upwards [ha,hu,hm,hn] with x ha hu hm hn
  have hmi := congrArg (fun v : VectorFourier.Vector => v i) hm
  have hni := congrArg (fun v : VectorFourier.Vector => v (WeakCurl.previous i)) hn
  simp only [PiLp.smul_apply, smul_eq_mul] at hmi hni
  change (StaticCoefficient.sqrtMultiplier c u) (VectorFourier.coordinateMap (unrotate x)) (WeakCurl.previous i) =
    (Real.sqrt (c.value (VectorFourier.coordinateMap (unrotate x))) : ℂ) * u (VectorFourier.coordinateMap (unrotate x)) (WeakCurl.previous i) at hni
  rw [hmi,coefficient_value,hu,ha,hni]

end OQ14.Packet06CyclicMaterial
#print axioms OQ14.Packet06CyclicMaterial.coefficient_value
#print axioms OQ14.Packet06CyclicMaterial.dielectric_value
#print axioms OQ14.Packet06CyclicMaterial.multiplier_action

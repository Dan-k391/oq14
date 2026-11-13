import Packet06TranslationNewton

/-! Actual coefficient and material multiplier under rigid translation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationMaterial
open MeasureTheory Metric Maxwell Packet06TranslationL2

def coefficient (a : Space) (c : StaticCoefficient.Coefficient) : StaticCoefficient.Coefficient where
  value := fun ξ => c.value (VectorFourier.coordinateMap (VectorFourier.coordinateMap.symm ξ-a))
  bound := c.bound
  measurable := c.measurable.comp (VectorFourier.coordinateMap.measurable.comp
    ((continuous_id.sub continuous_const).measurable.comp VectorFourier.coordinateMap.symm.measurable))
  nonnegative := fun _ => c.nonnegative _
  bounded := fun _ => c.bounded _

theorem coefficient_value (a : Space) (c : StaticCoefficient.Coefficient) (x : Space) :
    (coefficient a c).value (VectorFourier.coordinateMap x) = c.value (VectorFourier.coordinateMap (x-a)) := by
  simp [coefficient]

theorem dielectric_value (a : Space) (c : StaticCoefficient.Coefficient) (x : Space) :
    MaterialMaxwell.dielectric (coefficient a c) x = MaterialMaxwell.dielectric c (x-a) := by
  simp [MaterialMaxwell.dielectric, coefficient_value]

theorem coefficient_support (a : Space) (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    ∀ x : Space, x ∉ closedBall 0 (R+‖a‖) → (coefficient a c).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  rw [coefficient_value]
  apply hc
  intro hh
  apply hx
  simp only [mem_closedBall, dist_zero_right] at hh ⊢
  have h := norm_add_le (x-a) a
  have he : x-a+a = x := by abel
  rw [he] at h
  linarith

theorem multiplier_action (a : Space) (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) :
    StaticCoefficient.sqrtMultiplier (coefficient a c) (action a u) = action a (StaticCoefficient.sqrtMultiplier c u) := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have ha := action_ae a (StaticCoefficient.sqrtMultiplier c u) i
  have hu := action_ae a u i
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient a c) (action a u))
  have hn0 := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (StaticCoefficient.sqrtMultiplier_ae c u)
  have hn := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae hn0
  filter_upwards [ha,hu,hm,hn] with x ha hu hm hn
  have hmi := congrArg (fun v : VectorFourier.Vector => v i) hm
  have hni := congrArg (fun v : VectorFourier.Vector => v i) hn
  simp only [PiLp.smul_apply, smul_eq_mul] at hmi hni
  have hni' : (StaticCoefficient.sqrtMultiplier c u) (VectorFourier.coordinateMap (x-a)) i =
      (Real.sqrt (c.value (VectorFourier.coordinateMap (x-a))) : ℂ) * u (VectorFourier.coordinateMap (x-a)) i := by
    simpa only [sub_eq_add_neg] using hni
  rw [hmi,coefficient_value,hu,ha,hni']

theorem newton_action (a : Space) (u : VectorFourier.VectorL2) :
    NewtonL2.newtonOperator (action a u) = action a (NewtonL2.newtonOperator u) :=
  Packet06TranslationNewton.newton_action a u

theorem static_volume_conjugacy (a : Space) (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) :
    StaticNewton.volumeBlock (coefficient a c) (action a u) = action a (StaticNewton.volumeBlock c u) := by
  rw [StaticNewton.volumeBlock_eq, StaticNewton.volumeBlock_eq]
  unfold StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [multiplier_action]
  have hp : VectorFourier.physicalProjection (action a (StaticCoefficient.sqrtMultiplier c u)) =
      action a (VectorFourier.physicalProjection (StaticCoefficient.sqrtMultiplier c u)) := by
    have hh := newton_action a (StaticCoefficient.sqrtMultiplier c u)
    change -VectorFourier.physicalProjection (action a (StaticCoefficient.sqrtMultiplier c u)) =
      action a (-VectorFourier.physicalProjection (StaticCoefficient.sqrtMultiplier c u)) at hh
    simpa only [map_neg, neg_inj] using hh
  rw [hp, ← multiplier_action]

end OQ14.Packet06TranslationMaterial
#print axioms OQ14.Packet06TranslationMaterial.coefficient_value
#print axioms OQ14.Packet06TranslationMaterial.dielectric_value
#print axioms OQ14.Packet06TranslationMaterial.coefficient_support
#print axioms OQ14.Packet06TranslationMaterial.multiplier_action
#print axioms OQ14.Packet06TranslationMaterial.newton_action
#print axioms OQ14.Packet06TranslationMaterial.static_volume_conjugacy

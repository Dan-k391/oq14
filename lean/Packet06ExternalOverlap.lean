import Packet06ExternalHybridEquation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ExternalOverlap
open MeasureTheory Metric Maxwell Packet06LocalPencil Packet06ExternalFreeMaxwell
abbrev VectorL2 := VectorFourier.VectorL2

/-- Weighting by the actual compact material erases the difference between
source-generated local Green representatives on nested observation balls. -/
theorem weighted_free_overlap (c : StaticCoefficient.Coefficient) (z : ℂ) (J S T : ℝ)
    (hST : S ≤ T) (f : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    StaticCoefficient.sqrtMultiplier c (kernel z J T f) =
      StaticCoefficient.sqrtMultiplier c (kernel z J S f) := by
  let b := supportCoefficient J
  have he (U : ℝ) : response b z J U f = kernel z J U f := by
    change kernel z J U (StaticCoefficient.sqrtMultiplier b f) = _
    rw [supported_multiplier_identity J f hf]
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hov := (ae_restrict_iff' measurableSet_closedBall).mp
    (response_overlap b z J S T hST f (supportCoefficient_support J) i)
  simp only [he] at hov
  have ha := StaticNewton.material_source_ae c (kernel z J T f) i
  have hb := StaticNewton.material_source_ae c (kernel z J S f) i
  filter_upwards [hov,ha,hb,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c (kernel z J T f)) i,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c (kernel z J S f)) i]
    with x hov ha hb hpa hpb
  rw [← hpa,← hpb,ha,hb]
  by_cases hx : x ∈ closedBall (0 : Space) S
  · rw [hov hx]
  · rw [hc x hx]
    simp

#print axioms OQ14.Packet06ExternalOverlap.weighted_free_overlap
end OQ14.Packet06ExternalOverlap

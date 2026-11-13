import Packet07DrivenScalarEquation
import ConicalEntireGauge

/-! The actual material solution of a smooth entire illumination supplies its
scalar transmission data without separate incident or volume equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet07IncidentScalarEquation
open MeasureTheory Metric Set Maxwell WeakCurl DivCurlCompact
  ConicalGradientGraph Packet05RegionalDivergence Packet06ScalarGaussLocalization
open scoped SchwartzMap
abbrev Space := Maxwell.Space

theorem actual_incident_scalar_equation (c : StaticCoefficient.Coefficient)
    (k S : ℝ) (hk : k ≠ 0) (hS : 0 ≤ S)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius c S)
    (I : ConicalEntireGauge.Incident k)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (χ : ContDiffBump (0 : Space)) :
    let u := ConicalMaterialRunge.solutionOperator c k S (ConicalEntireGauge.restricted S I)
    let U := Packet06ComplexConePotential.potentialData (k : ℂ) S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    let W : Field := fun x i => I.E x i+Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x i
    ∃ hW : ∀ i, Continuous (fun x => W x i),
      CompactRepresentative (value χ U) ∧
      (∀ i, HasWeakPartial (value χ U) (gradient χ U i) i) ∧
      (∀ i, CompactRepresentative (correction χ W hW i)) ∧
      (∀ i, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
        gradient χ U i x+correction χ W hW i x=MaterialField.total c k u I.E x i) ∧
      HasDivergenceOn (ball (0 : Space) χ.rIn)
        (flux χ U W hW (Packet06MaxwellScalarEquation.epsilon c)
          (Packet06MaxwellScalarEquation.epsilon_memLp c)) 0 := by
  exact Packet07DrivenScalarEquation.actual_driven_scalar_equation c k S hk _ _ I.E I.H hc
    (ConicalMaterialRunge.weighted_actual c S _ I.E hc (ConicalEntireGauge.restricted_ae S I))
    (ConicalMaterialRunge.solution_equation c k S hS hfreq _)
    (fun i => (I.smoothE i).continuous)
    (fun i => (I.smoothH i).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
      (fun i => (I.smoothE i).of_le (by simp))
      (fun i => (I.smoothH i).of_le (by simp)) I.maxwell) χ

end OQ14.Packet07IncidentScalarEquation
#print axioms OQ14.Packet07IncidentScalarEquation.actual_incident_scalar_equation

import CommonUnionJointApprox
import ConicalCommonEntire

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.CommonIncidentSolutionBridge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.UnionFreeRunge
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem solution_eq (R k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (d : ComplexTransverseExpansion.ModeIndex →₀ ℂ) :
    ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) =
      UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
        (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d) := by
  let c := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep
  let I := FiniteAngularHerglotz.incident k d
  have hweighted : ConicalBallExtension.weighted c R (ConicalEntireGauge.restricted R I) =
      UnionMaterialTransfer.weighted c (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d) := by
    apply StaticSphereMaterial.vector_ext_physical
    intro j
    have h1 := ConicalMaterialRunge.weighted_actual c R _ _
      (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR)
      (ConicalEntireGauge.restricted_ae R I) j
    have h2 := UnionMaterialTransfer.weighted_actual c (balls center a) (balls_compact center a).measurableSet _ _
      (UnionMaterialTransfer.common_support_union p a center B hB hcontrast ha hsep)
      (UnionFiniteAngularRunge.incident_ae k R (balls center a) hKR d) j
    exact h1.trans h2.symm
  change Ring.inverse (DynamicVolume.volumeBlock c k R)
    (ConicalBallExtension.weighted c R (ConicalEntireGauge.restricted R I)) =
    Ring.inverse (DynamicVolume.volumeBlock c k R)
      (UnionMaterialTransfer.weighted c (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d))
  rw [hweighted]
end OQ14.CommonIncidentSolutionBridge
#print axioms OQ14.CommonIncidentSolutionBridge.solution_eq

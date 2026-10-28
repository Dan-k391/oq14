import CommonIncidentSolutionBridge
import ConicalCommonFixedGauge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.CommonTotalError
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.UnionFreeRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def solutionDifference (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R) (d : Input) :=
  UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
    (balls center a) (balls_compact center a).measurableSet
    (UnionFiniteAngularRunge.incident k R (balls center a) hKR d) -
    ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k

def errorField (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) :=
  UnionMaterialTransfer.vector (balls center a) (balls_compact center a).measurableSet
    (ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR hT d) +
  (newtonOperator + DynamicConvolution.operator k (2*R))
    (StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d))

omit [DecidableEq ι] in
theorem errorField_bound (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) :
    ‖errorField p a center B hB hcontrast ha hsep i R T k hKR hT d‖ ≤
      ‖UnionMaterialTransfer.vector (balls center a) (balls_compact center a).measurableSet‖ *
        ‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR hT d‖ +
      ‖(newtonOperator + DynamicConvolution.operator k (2*R)).comp
        (StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))‖ *
        ‖solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d‖ := by
  unfold errorField
  apply (norm_add_le _ _).trans
  exact add_le_add ((UnionMaterialTransfer.vector _ _).le_opNorm _)
    (((newtonOperator + DynamicConvolution.operator k (2*R)).comp
      (StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))).le_opNorm _)
end OQ14.CommonTotalError
#print axioms OQ14.CommonTotalError.errorField_bound




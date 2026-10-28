import CommonIncidentSolutionBridge
import ConicalCommonErrorNorm

/-! Joint Runge approximation controls the actual common-material solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.CommonActualJointApprox
open MeasureTheory Set Metric OQ14.NewtonL2 OQ14.UnionFreeRunge
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem joint_actual (i : ι) (R T k : ℝ) (hk : 0 < k)
    (hR0 : 0 ≤ R) (hRT : R ≤ T) (hra : ∀ j, 0 ≤ a j)
    (hgeom : ∀ j l, j ≠ l → a j+a l < dist (center j) (center l))
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ComplexTransverseExpansion.ModeIndex →₀ ℂ,
      ‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR ((hR i).trans (closedBall_subset_closedBall hRT)) d‖ < ε ∧
      ‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ < ε := by
  obtain ⟨d,hinc,hsol⟩ := CommonUnionJointApprox.joint_approximation p a center B hB hcontrast ha hsep i R T k hk
    hR0 hRT hra hgeom hKR ((hR i).trans (closedBall_subset_closedBall hRT)) hai ε hε
  refine ⟨d, ?_, ?_⟩
  · exact hinc
  · rw [CommonIncidentSolutionBridge.solution_eq p a center B hB hcontrast ha hsep R k hKR hR]
    exact hsol

end OQ14.CommonActualJointApprox
#print axioms OQ14.CommonActualJointApprox.joint_actual

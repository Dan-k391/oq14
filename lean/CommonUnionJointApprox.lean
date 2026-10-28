import CommonUnionTarget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CommonUnionJointApprox
open MeasureTheory Set Metric OQ14.NewtonL2 OQ14.UnionFreeRunge
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem joint_approximation (i : ι) (R T k : ℝ) (hk : 0 < k)
    (hR : 0 ≤ R) (hRT : R ≤ T) (hra : ∀ j, 0 ≤ a j)
    (hgeom : ∀ j l, j ≠ l → a j+a l < dist (center j) (center l))
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ComplexTransverseExpansion.ModeIndex →₀ ℂ,
      ‖UnionFiniteAngularRunge.incident k R (balls center a) hKR d +
        target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
          (ConicalCommonMaterial.source p a center i)
          (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
          (ConicalCommonBaseline.source_ae p a center i)‖ < ε ∧
      ‖UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
        (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ < ε := by
  let K := balls center a
  let A := UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
    K (balls_compact center a).measurableSet
  let v := target k R T K hKR (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonBaseline.source_ae p a center i)
  let δ := ε/(‖A‖+2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨d,hd⟩ := UnionFiniteAngularRunge.approximation center a hra hgeom k hk R T hR hRT hKR
    (ConicalCommonBaseline.forcing p a center i) (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonMaterial.source_zero_union p a center ha hsep hai i)
    (ConicalCommonBaseline.source_ae p a center i) δ hδ
  change ‖UnionFiniteAngularRunge.incident k R K hKR d-v‖ < δ at hd
  have hAv : A v = -ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k :=
    CommonUnionTarget.solution_target_eq p a center B hB hcontrast ha hsep i R T k hKR hT
  refine ⟨-d,?_,?_⟩
  · rw [CommonUnionTarget.incident_neg]
    change ‖-UnionFiniteAngularRunge.incident k R K hKR d+v‖ < ε
    have he : -UnionFiniteAngularRunge.incident k R K hKR d+v =
      -(UnionFiniteAngularRunge.incident k R K hKR d-v) := by abel
    rw [he,norm_neg]
    have hde : δ < ε := by
      dsimp [δ]
      have hp : 1 < ‖A‖+2 := by have := norm_nonneg A; linarith
      exact (div_lt_self hε hp)
    exact hd.trans hde
  · rw [CommonUnionTarget.incident_neg, map_neg]
    change ‖-A (UnionFiniteAngularRunge.incident k R K hKR d)-
      ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ < ε
    have hs : ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k = -A v := by
      rw [hAv,neg_neg]
    rw [hs]
    have he : -A (UnionFiniteAngularRunge.incident k R K hKR d) - -A v =
      -(A (UnionFiniteAngularRunge.incident k R K hKR d)-A v) := by abel
    rw [he,norm_neg,← map_sub]
    apply (A.le_opNorm _).trans_lt
    have hmul := mul_le_mul_of_nonneg_left hd.le (norm_nonneg A)
    have hkey : (‖A‖+2)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
end OQ14.CommonUnionJointApprox
#print axioms OQ14.CommonUnionJointApprox.joint_approximation


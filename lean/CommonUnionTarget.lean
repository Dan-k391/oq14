import UnionMaterialTransfer
import ConicalCommonDynamic
import ConicalNormalizedInputTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OQ14.CommonUnionTarget
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.UnionFreeRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [Fintype ι] [DecidableEq ι] in
theorem target_negative_incident (i : ι) (R T k : ℝ)
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (j : Fin 3) :
    (target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
      (ConicalCommonMaterial.source p a center i)
      (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
      (ConicalCommonBaseline.source_ae p a center i) j : Space → ℂ) =ᵐ[volume.restrict (balls center a)]
      fun x => -(physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j x) := by
  have ht := (target_memLp k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonBaseline.source_ae p a center i) j).coeFn_toLp
  have hi := (ConicalCommonDynamic.incident_ae p a center i R T k hT (ha i) j).filter_mono
    (ae_mono (Measure.restrict_mono_set volume hKR))
  filter_upwards [ht,hi] with x ht hi
  change ((target_memLp k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonBaseline.source_ae p a center i) j).toLp _) x = _
  rw [ht,hi]
  simp

theorem weighted_target_eq (i : ι) (R T k : ℝ)
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) :
    UnionMaterialTransfer.weighted (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (balls center a) (balls_compact center a).measurableSet
      (target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
        (ConicalCommonMaterial.source p a center i)
        (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
        (ConicalCommonBaseline.source_ae p a center i)) =
      -ConicalCommonDynamic.weightedForcing p a center B hB hcontrast ha hsep i R T k := by
  have hg (j : Fin 3) : (target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
      (ConicalCommonMaterial.source p a center i)
      (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
      (ConicalCommonBaseline.source_ae p a center i) j : Space → ℂ) =ᵐ[volume.restrict (balls center a)]
      (physicalCoordinate (-ConicalCommonDynamic.incident p a center i R T k) j : Space → ℂ) := by
    have h := target_negative_incident p a center ha i R T k hKR hT j
    rw [physicalCoordinate_neg]
    filter_upwards [h, ae_restrict_of_ae (Lp.coeFn_neg (physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j))] with x h hn
    rw [h,hn]
    rfl
  have h := UnionMaterialTransfer.weighted_eq_global
    (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) (balls center a)
    (balls_compact center a).measurableSet _ (-ConicalCommonDynamic.incident p a center i R T k)
    (UnionMaterialTransfer.common_support_union p a center B hB hcontrast ha hsep) hg
  simpa only [ConicalCommonDynamic.weightedForcing, map_neg] using h
theorem solution_target_eq (i : ι) (R T k : ℝ)
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) :
    UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
      (balls center a) (balls_compact center a).measurableSet
      (target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
        (ConicalCommonMaterial.source p a center i)
        (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
        (ConicalCommonBaseline.source_ae p a center i)) =
      -ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k := by
  change Ring.inverse (DynamicVolume.volumeBlock (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R)
    (UnionMaterialTransfer.weighted (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (balls center a) (balls_compact center a).measurableSet _) = _
  rw [weighted_target_eq p a center B hB hcontrast ha hsep i R T k hKR hT, map_neg]
  rfl
theorem incident_neg (k R : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R)
    (d : ComplexTransverseExpansion.ModeIndex →₀ ℂ) :
    UnionFiniteAngularRunge.incident k R K hKR (-d) = -UnionFiniteAngularRunge.incident k R K hKR d := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [UnionFiniteAngularRunge.incident_ae k R K hKR (-d) j,
    UnionFiniteAngularRunge.incident_ae k R K hKR d j,
    Lp.coeFn_neg (UnionFiniteAngularRunge.incident k R K hKR d j)] with x h1 h2 hn
  change (UnionFiniteAngularRunge.incident k R K hKR (-d) j : Space → ℂ) x =
    (-UnionFiniteAngularRunge.incident k R K hKR d j : Scalar K) x
  rw [h1,hn]
  simp only [Pi.neg_apply,h2]
  have hh := ConicalNormalizedInputTransfer.incident_E_smul k (-1) d x j
  simpa using hh
theorem approximate_baseline_solution (i : ι) (R T k : ℝ) (hk : 0 < k)
    (hR : 0 ≤ R) (hRT : R ≤ T) (hra : ∀ j, 0 ≤ a j)
    (hgeom : ∀ j l, j ≠ l → a j+a l < dist (center j) (center l))
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ComplexTransverseExpansion.ModeIndex →₀ ℂ,
      ‖UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
        (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ < ε := by
  obtain ⟨d,hd⟩ := UnionMaterialTransfer.finite_angular_solution_approximation center a hra hgeom
    (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k hk R T hR hRT hKR
    (ConicalCommonBaseline.forcing p a center i) (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonMaterial.source_zero_union p a center ha hsep hai i)
    (ConicalCommonBaseline.source_ae p a center i) ε hε
  refine ⟨-d,?_⟩
  rw [incident_neg, map_neg]
  rw [solution_target_eq p a center B hB hcontrast ha hsep i R T k hKR hT] at hd
  have he : -(UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
      (balls center a) (balls_compact center a).measurableSet
      (UnionFiniteAngularRunge.incident k R (balls center a) hKR d)) -
      ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k =
      -((UnionMaterialTransfer.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
        (balls center a) (balls_compact center a).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center a) hKR d)) -
        -ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k) := by abel
  rw [he,norm_neg]
  exact hd
end OQ14.CommonUnionTarget
#print axioms OQ14.CommonUnionTarget.target_negative_incident

#print axioms OQ14.CommonUnionTarget.weighted_target_eq


#print axioms OQ14.CommonUnionTarget.solution_target_eq


#print axioms OQ14.CommonUnionTarget.incident_neg


#print axioms OQ14.CommonUnionTarget.approximate_baseline_solution



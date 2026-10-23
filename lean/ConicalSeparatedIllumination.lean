import ConicalMaterialRunge
import ConicalSeparatedDynamic

/-! Genuine finite Maxwell illuminations approximate the negative separated incident and its material response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalSeparatedIllumination
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalRungeBall OQ14.ConicalRungeClosure OQ14.ConicalMaterialRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def incidentBall (p : Data) (a k : ℝ) : BallL2 a :=
  ConicalBallRestriction.vector a (ConicalSeparatedDynamic.incident p a k)

theorem incidentBall_eq_neg_target (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) :
    incidentBall p a k= -target k a p.cutoff.rOut (ConicalSeparatedSource.forcing p a)
      (ConicalSeparatedSource.physicalSource p a)
      (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.forcing_ae p a) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [ConicalBallRestriction.vector_ae a (ConicalSeparatedDynamic.incident p a k) j,
    ConicalSeparatedDynamic.incident_ae p a k hai j,
    target_component_ae k a p.cutoff.rOut (ConicalSeparatedSource.forcing p a)
      (ConicalSeparatedSource.physicalSource p a)
      (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.forcing_ae p a) j,
    Lp.coeFn_neg (target k a p.cutoff.rOut (ConicalSeparatedSource.forcing p a)
      (ConicalSeparatedSource.physicalSource p a)
      (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.forcing_ae p a) j)] with x hr hi ht hn
  change (incidentBall p a k j) x=(-target _ _ _ _ _ _ _ j) x
  dsimp only [incidentBall]
  rw [hr,hi,hn]
  simp only [Pi.neg_apply,ht]

theorem incidentBall_mem_closedSpan (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hk : 0 < k) :
    incidentBall p a k ∈ (waveSpan k a).topologicalClosure := by
  rw [incidentBall_eq_neg_target p a k hai]
  apply Submodule.neg_mem
  exact target_mem_closedSpan k hk a p.cutoff.rOut ha (hai.trans p.cutoff.rIn_lt_rOut).le
    (ConicalSeparatedSource.forcing p a) (ConicalSeparatedSource.physicalSource p a)
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_zero_material p a hai) (ConicalSeparatedSource.forcing_ae p a)

theorem finite_incident_approximation (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : WaveIndex →₀ ℂ, ‖ConicalFinitePlanes.restricted k a b-incidentBall p a k‖ < ε := by
  have ht := incidentBall_mem_closedSpan p a k ha hai hk
  change incidentBall p a k ∈ closure (waveSpan k a : Set (BallL2 a)) at ht
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp ht ε hε
  obtain ⟨b,hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨b,?_⟩
  dsimp only [ConicalFinitePlanes.restricted]
  rw [hb]
  simpa only [dist_eq_norm,norm_sub_rev] using hd

theorem weighted_restriction (c : StaticCoefficient.Coefficient) (a : ℝ) (I : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0) :
    ConicalBallExtension.weighted c a (ConicalBallRestriction.vector a I)=StaticCoefficient.sqrtMultiplier c I := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro j
  apply VectorFourier.scalarCoordinates.injective
  apply Lp.ext
  have hl := (ae_restrict_iff' measurableSet_closedBall).mp (ConicalBallRestriction.vector_ae a I j)
  filter_upwards [StaticNewton.material_source_ae c (ConicalBallExtension.vector a (ConicalBallRestriction.vector a I)) j,
    StaticNewton.material_source_ae c I j,
    ConicalBallExtension.vector_ae a (ConicalBallRestriction.vector a I) j,
    NewtonL2.physicalCoordinate_ae (ConicalBallExtension.vector a (ConicalBallRestriction.vector a I)) j,
    NewtonL2.physicalCoordinate_ae I j,hl] with x he hi hx hp hI hl
  change NewtonL2.physicalCoordinate (ConicalBallExtension.weighted c a (ConicalBallRestriction.vector a I)) j x=
    NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c I) j x
  change NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c (ConicalBallExtension.vector a (ConicalBallRestriction.vector a I))) j x=_
  rw [he,hi,← hp,hx]
  by_cases h : x ∈ closedBall (0 : Space) a
  · rw [indicator_of_mem h,hl h,hI]
  · rw [hc x h]
    simp

theorem solution_restriction (c : StaticCoefficient.Coefficient) (k a : ℝ) (I : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0) :
    solutionOperator c k a (ConicalBallRestriction.vector a I)=MaterialVolumeLimit.weightedSolution c k a I := by
  change Ring.inverse (DynamicVolume.volumeBlock c k a)
    (ConicalBallExtension.weighted c a (ConicalBallRestriction.vector a I))=_
  rw [weighted_restriction c a I hc]
  rfl

theorem total_restriction (c : StaticCoefficient.Coefficient) (k a : ℝ) (I : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0) :
    totalOperator c k a (ConicalBallRestriction.vector a I)=
      ConicalBallRestriction.vector a (MaterialVolumeLimit.volumeField c k a I) := by
  simp only [totalOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,solution_restriction c k a I hc,MaterialVolumeLimit.volumeField,map_add]

theorem finite_total_approximation (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hk : 0 < k) (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : WaveIndex →₀ ℂ,
      ‖totalOperator c k a (ConicalFinitePlanes.restricted k a b)-
        ConicalBallRestriction.vector a (MaterialVolumeLimit.volumeField c k a (ConicalSeparatedDynamic.incident p a k))‖ < ε := by
  let A := totalOperator c k a
  have hA : 0 < ‖A‖+1 := by positivity
  obtain ⟨b,hb⟩ := finite_incident_approximation p a k ha hai hk (ε/(‖A‖+1)) (div_pos hε hA)
  refine ⟨b,?_⟩
  rw [← total_restriction c k a _ hc]
  change ‖A (ConicalFinitePlanes.restricted k a b)-A (incidentBall p a k)‖ < ε
  have he := A.le_opNorm (ConicalFinitePlanes.restricted k a b-incidentBall p a k)
  rw [map_sub] at he
  apply he.trans_lt
  calc
    _ ≤ (‖A‖+1)*‖ConicalFinitePlanes.restricted k a b-incidentBall p a k‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖A‖+1)*(ε/(‖A‖+1)) := mul_lt_mul_of_pos_left hb hA
    _ = ε := mul_div_cancel₀ _ hA.ne'

end OQ14.ConicalSeparatedIllumination

#print axioms OQ14.ConicalSeparatedIllumination.incidentBall_eq_neg_target
#print axioms OQ14.ConicalSeparatedIllumination.incidentBall_mem_closedSpan
#print axioms OQ14.ConicalSeparatedIllumination.finite_incident_approximation
#print axioms OQ14.ConicalSeparatedIllumination.weighted_restriction
#print axioms OQ14.ConicalSeparatedIllumination.solution_restriction
#print axioms OQ14.ConicalSeparatedIllumination.total_restriction
#print axioms OQ14.ConicalSeparatedIllumination.finite_total_approximation

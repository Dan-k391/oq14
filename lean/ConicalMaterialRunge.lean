import ConicalBallRestriction
import ConicalFinitePlanes
import IncidentLocalization
import MaterialMaxwell

/-! Actual bounded material solution map on physical ball incident data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalMaterialRunge
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalRungeBall OQ14.ConicalRungeClosure
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def solutionOperator (c : StaticCoefficient.Coefficient) (k a : ℝ) : BallL2 a →L[ℂ] VectorL2 :=
  (Ring.inverse (DynamicVolume.volumeBlock c k a)).comp (ConicalBallExtension.weighted c a)

def totalOperator (c : StaticCoefficient.Coefficient) (k a : ℝ) : BallL2 a →L[ℂ] BallL2 a :=
  ContinuousLinearMap.id ℂ (BallL2 a)+(ConicalBallRestriction.vector a).comp
    ((NewtonL2.newtonOperator+DynamicConvolution.operator k (2*a)).comp
      ((StaticCoefficient.sqrtMultiplier c).comp (solutionOperator c k a)))

theorem weighted_actual (c : StaticCoefficient.Coefficient) (a : ℝ) (g : BallL2 a) (I : Field)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0)
    (hg : ∀ j, (g j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => I x j) (j : Fin 3) :
    (fun x => ConicalBallExtension.weighted c a g (VectorFourier.coordinateMap x) j) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*I x j := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (ConicalBallExtension.vector a g))
  have hl := (ae_restrict_iff' measurableSet_closedBall).mp (hg j)
  filter_upwards [hs,NewtonL2.physicalCoordinate_ae (ConicalBallExtension.vector a g) j,
    ConicalBallExtension.vector_ae a g j,hl] with x hs hp he hl
  change StaticCoefficient.sqrtMultiplier c (ConicalBallExtension.vector a g) (VectorFourier.coordinateMap x) j=_
  rw [hs]
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
    ConicalBallExtension.vector a g (VectorFourier.coordinateMap x) j=_
  rw [← hp,he]
  by_cases hx : x ∈ closedBall (0 : Space) a
  · rw [indicator_of_mem hx,hl hx]
  · rw [hc x hx]
    simp

theorem solution_equation (c : StaticCoefficient.Coefficient) (k a : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius c a) (g : BallL2 a) :
    DynamicVolume.volumeBlock c k a (solutionOperator c k a g)=ConicalBallExtension.weighted c a g :=
  MaterialField.solution_equation c k a ha (by
    have he := DynamicStaticLimit.error_small c k a hk
    linarith) _

theorem total_ae (c : StaticCoefficient.Coefficient) (k a : ℝ) (g : BallL2 a) (I : Field)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0)
    (hg : ∀ j, (g j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => I x j) (j : Fin 3) :
    (totalOperator c k a g j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => MaterialField.total c k (solutionOperator c k a g) I x j := by
  let F := StaticCoefficient.sqrtMultiplier c (solutionOperator c k a g)
  let G := (NewtonL2.newtonOperator+DynamicConvolution.operator k (2*a)) F
  have he := LocalVolumeResponse.electric_ae_on_ball k a a F
    (DynamicVolume.source c (solutionOperator c k a g))
    (DynamicVolume.source_integrable c _ a hc) (DynamicVolume.source_zero c _ a hc)
    (StaticNewton.material_source_ae c _) j
  have he' : NewtonL2.physicalCoordinate G j =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => MaterialField.scattered c k (solutionOperator c k a g) x j := by
    simpa only [G,F,LocalVolumeResponse.localRepresentative,two_mul,ContinuousLinearMap.add_apply] using he
  change ((g j)+(ConicalBallRestriction.vector a G j) : ScalarBall a) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add (g j) (ConicalBallRestriction.vector a G j),
    ConicalBallRestriction.vector_ae a G j,he',hg j] with x hadd hr he hg
  rw [hadd]
  simp only [Pi.add_apply,hr,he,hg,MaterialField.total]

theorem finite_solution_maxwell (c : StaticCoefficient.Coefficient) (k a : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius c a)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) a → c.value (VectorFourier.coordinateMap x)=0)
    (b : WaveIndex →₀ ℂ) :
    MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric c)
      (MaterialField.total c k (solutionOperator c k a (ConicalFinitePlanes.restricted k a b)) (ConicalFinitePlanes.electric k b))
      (MaterialMaxwell.totalMagnetic c k (solutionOperator c k a (ConicalFinitePlanes.restricted k a b)) (ConicalFinitePlanes.magnetic k b)) := by
  exact MaterialMaxwell.volume_solution_testMaxwell c k a _ _ _ _ hc
    (weighted_actual c a _ _ hc (ConicalFinitePlanes.restricted_ae k a b))
    (solution_equation c k a ha hk _)
    (fun j => (ConicalFinitePlanes.electric_smooth k b j).continuous.locallyIntegrable)
    (fun j => (ConicalFinitePlanes.magnetic_smooth k b j).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k _ _
      (fun j => (ConicalFinitePlanes.electric_smooth k b j).of_le (by simp))
      (fun j => (ConicalFinitePlanes.magnetic_smooth k b j).of_le (by simp))
      (ConicalFinitePlanes.maxwell_at k b))

theorem finite_total_approximation (c : StaticCoefficient.Coefficient) (k : ℝ) (hk : 0 < k)
    (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T) (G : VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hσin : ∀ j x, x ∈ closedBall (0 : Space) a → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : WaveIndex →₀ ℂ,
      ‖totalOperator c k a (ConicalFinitePlanes.restricted k a b)-totalOperator c k a (target k a T G σ hcσ hG)‖ < ε := by
  let A := totalOperator c k a
  have hA : 0 < ‖A‖+1 := by positivity
  obtain ⟨b,hb⟩ := ConicalRungeClosure.finite_approximation k hk a T ha haT G σ hcσ hσin hG
    (ε/(‖A‖+1)) (div_pos hε hA)
  refine ⟨b,?_⟩
  have he := A.le_opNorm (ConicalFinitePlanes.restricted k a b-target k a T G σ hcσ hG)
  rw [map_sub] at he
  apply he.trans_lt
  calc
    _ ≤ (‖A‖+1)*‖ConicalFinitePlanes.restricted k a b-target k a T G σ hcσ hG‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖A‖+1)*(ε/(‖A‖+1)) := mul_lt_mul_of_pos_left hb hA
    _ = ε := mul_div_cancel₀ _ hA.ne'

end OQ14.ConicalMaterialRunge

#print axioms OQ14.ConicalMaterialRunge.weighted_actual
#print axioms OQ14.ConicalMaterialRunge.solution_equation
#print axioms OQ14.ConicalMaterialRunge.total_ae
#print axioms OQ14.ConicalMaterialRunge.finite_solution_maxwell
#print axioms OQ14.ConicalMaterialRunge.finite_total_approximation

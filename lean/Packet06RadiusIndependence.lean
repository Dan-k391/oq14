import Packet06CyclicReciprocal

/-! The actual compactly supported material volume block is independent of
    which enclosing radius is used in its dyadic truncation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RadiusIndependence
open MeasureTheory Filter Set Metric
open scoped Topology

theorem real_radius_independent (c : StaticCoefficient.Coefficient) (k R T : ℝ)
    (hR : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hT : ∀ x : Maxwell.Space, x ∉ closedBall 0 T → c.value (VectorFourier.coordinateMap x) = 0) :
    DynamicVolume.volumeBlock c k R = DynamicVolume.volumeBlock c k T := by
  apply ContinuousLinearMap.ext
  intro u
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hr := DynamicVolume.volumeBlock_actual c u k R hR i
  have ht := DynamicVolume.volumeBlock_actual c u k T hT i
  filter_upwards [hr,ht] with x hr ht
  exact hr.trans ht.symm

theorem complex_radius_independent (c : StaticCoefficient.Coefficient) (R T : ℝ)
    (hR0 : 0 ≤ R) (hT0 : 0 ≤ T)
    (hR : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hT : ∀ x : Maxwell.Space, x ∉ closedBall 0 T → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) :
    ComplexConvolutionAnalytic.volumeBlock c z R = ComplexConvolutionAnalytic.volumeBlock c z T := by
  let L : ℂ → VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 := fun w => ComplexConvolutionAnalytic.volumeBlock c w R
  let M : ℂ → VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 := fun w => ComplexConvolutionAnalytic.volumeBlock c w T
  have heq (t : ℝ) : L t = M t := by
    change ComplexConvolutionAnalytic.volumeBlock c (t : ℂ) R = ComplexConvolutionAnalytic.volumeBlock c (t : ℂ) T
    rw [ComplexConvolutionAnalytic.volumeBlock_ofReal, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact real_radius_independent c t R T hR hT
  have hl : AnalyticOnNhd ℂ L univ := fun w _ => (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR0).analyticAt w
  have hm : AnalyticOnNhd ℂ M univ := fun w _ => (ComplexConvolutionAnalytic.volumeBlock_differentiable c T hT0).analyticAt w
  have hclosure : (1 : ℂ) ∈ closure ({w | L w = M w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let t : ℝ := 1+ε/2
    have ht : (t : ℂ) ≠ 1 := by
      have h : t ≠ 1 := by dsimp [t]; linarith
      exact_mod_cast h
    refine ⟨(t : ℂ), ⟨heq t, ht⟩, ?_⟩
    have hsub : (t : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [t]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact hl.eqOn_of_preconnected_of_mem_closure hm isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

end OQ14.Packet06RadiusIndependence
#print axioms OQ14.Packet06RadiusIndependence.real_radius_independent
#print axioms OQ14.Packet06RadiusIndependence.complex_radius_independent

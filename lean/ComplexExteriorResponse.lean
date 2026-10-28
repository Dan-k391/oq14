import ComplexResponseRealWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexExteriorResponse
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexResponseTests OQ14.ComplexResponseRealWeak
open scoped SchwartzMap Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def response (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) : VectorL2 :=
  NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u) +
    ComplexConvolutionAnalytic.operator z (T+S) (StaticCoefficient.sqrtMultiplier c u)

theorem response_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2) :
    Differentiable ℂ (fun z => response c z S T u) := by
  unfold response
  exact (differentiable_const _).add
    ((ComplexConvolutionAnalytic.operator_differentiable (T+S) hST).clm_apply (differentiable_const _))

theorem test_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2) (i : Fin 3) (f : 𝓢(Space, ℂ)) :
    Differentiable ℂ (fun z => testPair i f (response c z S T u)) :=
  (testPair i f).differentiable.comp (response_differentiable c S T hST u)

theorem real_ball (c : Coefficient) (k S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x : Space => response c (k : ℂ) S T u (VectorFourier.coordinateMap x) i)
      =ᵐ[volume.restrict (closedBall 0 T)] fun x => MaterialField.scattered c k u x i := by
  have h := LocalVolumeResponse.electric_ae_on_ball k T S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i
  have he := ae_restrict_of_ae (s := closedBall (0 : Space) T) (NewtonL2.physicalCoordinate_ae
    (LocalVolumeResponse.localRepresentative k T S (StaticCoefficient.sqrtMultiplier c u)) i)
  filter_upwards [h, he] with x hx hy
  have hr : response c (k : ℂ) S T u = LocalVolumeResponse.localRepresentative k T S (StaticCoefficient.sqrtMultiplier c u) := by
    simp only [response, ComplexConvolutionAnalytic.operator_ofReal, LocalVolumeResponse.localRepresentative]
  rw [hr, ← hy, hx]
  rfl

theorem real_test (c : Coefficient) (k S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    testPair i f.val (response c (k : ℂ) S T u) =
      ∫ x, MaterialField.scattered c k u x i * f.val x := by
  rw [testPair_integral]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (real_ball c k S T u hc i)] with x hx
  by_cases hxb : x ∈ closedBall (0 : Space) T
  · rw [hx hxb]
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hxb (hf h))
    simp [hz]

def residual (c : Coefficient) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) (z : ℂ) : ℂ :=
  (∑ l : Fin 3, testPair l (testPartial l (testPartial i f)).val (response c z S T u)) -
  (∑ l : Fin 3, testPair i (testPartial l (testPartial l f)).val (response c z S T u)) -
    z^2 * testPair i f.val (response c z S T u) -
    z^2 * (∫ x, DynamicVolume.source c u i x * f.val x)

theorem residual_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2) (i : Fin 3) (f : Test) : Differentiable ℂ (residual c S T u i f) := by
  unfold residual
  apply Differentiable.sub
  · apply Differentiable.sub
    · apply Differentiable.sub
      · exact Differentiable.sum fun l _ => test_differentiable c S T hST u l _
      · exact Differentiable.sum fun l _ => test_differentiable c S T hST u i _
    · exact (differentiable_id.pow 2).mul (test_differentiable c S T hST u i _)
  · exact (differentiable_id.pow 2).mul (differentiable_const _)

theorem residual_real_zero (c : Coefficient) (S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) (k : ℝ) :
    residual c S T u i f k = 0 := by
  have hs (a b : Fin 3) : tsupport ((testPartial a (testPartial b f)).val : Space → ℂ) ⊆ closedBall 0 T :=
    (partial_support a _).trans ((partial_support b _).trans hf)
  unfold residual
  simp_rw [real_test c k S T u hc _ _ (hs _ _), real_test c k S T u hc i f hf]
  have h := FieldResponse.electric_maxwell_source k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (MaterialField.source_compact c u S hc) (StaticNewton.material_source_ae c u) i f
  dsimp only [MaterialField.scattered]
  linear_combination h

theorem residual_zero (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) (z : ℂ) :
    residual c S T u i f z = 0 := by
  have hclosure : (1 : ℂ) ∈ closure ({w | residual c S T u i f w = (0 : ℂ)} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1 + ε/2
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨residual_real_zero c S T u hc i f hf r, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ (residual c S T u i f) Set.univ from
    fun w _ => (residual_differentiable c S T hST u i f).analyticAt w).eqOn_of_preconnected_of_mem_closure
      (fun w _ => analyticAt_const) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

#print axioms OQ14.ComplexExteriorResponse.response_differentiable
#print axioms OQ14.ComplexExteriorResponse.real_ball
#print axioms OQ14.ComplexExteriorResponse.residual_zero
end OQ14.ComplexExteriorResponse

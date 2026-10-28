import ComplexResponseTests
import RegionalMaxwellHelmholtz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexResponseRealWeak
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ComplexResponseTests
open scoped SchwartzMap Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem partial_support (i : Fin 3) (f : Test) :
    tsupport ((testPartial i f).val : Space → ℂ) ⊆ tsupport (f.val : Space → ℂ) := by
  change tsupport (fun x => dcoord f.val x i) ⊆ tsupport (f.val : Space → ℂ)
  exact RegionalMaxwellHelmholtz.partial_tsupport f.val i

theorem real_testPair (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 R) :
    testPair i f.val (response c (k : ℂ) R u) =
      ∫ x, MaterialField.scattered c k u x i * f.val x := by
  rw [testPair_integral]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (real_response_ball c k R u hc i)] with x hx
  by_cases hxb : x ∈ closedBall (0 : Space) R
  · rw [hx hxb]
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hxb (hf h))
    simp [hz]

def residual (c : Coefficient) (R : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) (z : ℂ) : ℂ :=
  (∑ l : Fin 3, testPair l (testPartial l (testPartial i f)).val (response c z R u)) -
  (∑ l : Fin 3, testPair i (testPartial l (testPartial l f)).val (response c z R u)) -
    z^2 * testPair i f.val (response c z R u) -
    z^2 * (∫ x, DynamicVolume.source c u i x * f.val x)

theorem residual_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorL2) (i : Fin 3) (f : Test) : Differentiable ℂ (residual c R u i f) := by
  unfold residual
  apply Differentiable.sub
  · apply Differentiable.sub
    · apply Differentiable.sub
      · exact Differentiable.sum fun l _ => response_test_differentiable c R hR u l _
      · exact Differentiable.sum fun l _ => response_test_differentiable c R hR u i _
    · exact (differentiable_id.pow 2).mul (response_test_differentiable c R hR u i _)
  · exact (differentiable_id.pow 2).mul (differentiable_const _)

theorem residual_real_zero (c : Coefficient) (R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 R) (k : ℝ) :
    residual c R u i f k = 0 := by
  have hs (a b : Fin 3) : tsupport ((testPartial a (testPartial b f)).val : Space → ℂ) ⊆ closedBall 0 R :=
    (partial_support a _).trans ((partial_support b _).trans hf)
  unfold residual
  simp_rw [real_testPair c k R u hc _ _ (hs _ _), real_testPair c k R u hc i f hf]
  have h := FieldResponse.electric_maxwell_source k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (MaterialField.source_compact c u R hc) (StaticNewton.material_source_ae c u) i f
  dsimp only [MaterialField.scattered]
  linear_combination h

theorem residual_zero (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 R) (z : ℂ) :
    residual c R u i f z = 0 := by
  have hclosure : (1 : ℂ) ∈ closure ({w | residual c R u i f w = (0 : ℂ)} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1 + ε/2
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨residual_real_zero c R u hc i f hf r, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have h := (show AnalyticOnNhd ℂ (residual c R u i f) Set.univ from
    fun w _ => (residual_differentiable c R hR u i f).analyticAt w).eqOn_of_preconnected_of_mem_closure
      (fun w _ => analyticAt_const) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)
  exact h

#print axioms OQ14.ComplexResponseRealWeak.residual_zero
#print axioms OQ14.ComplexResponseRealWeak.residual_differentiable
#print axioms OQ14.ComplexResponseRealWeak.residual_real_zero
end OQ14.ComplexResponseRealWeak




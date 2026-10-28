import ComplexMagneticResponse
import ComplexExteriorResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticMaxwell
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexResponseTests OQ14.ComplexResponseRealWeak
open OQ14.WeakCurl (next previous)
open scoped SchwartzMap Topology InnerProductSpace
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def electricPair (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  testPair i f.val (ComplexExteriorResponse.response c z S T u)

def magneticPair (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  ⟪FourierL2.embed (NewtonL2.conjugate f.val), ComplexMagneticResponse.response c z S T u i⟫_ℂ

theorem electricPair_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2) (i : Fin 3) (f : Test) : Differentiable ℂ (fun z => electricPair c z S T u i f) :=
  ComplexExteriorResponse.test_differentiable c S T hST u i f.val

theorem magneticPair_differentiable (c : Coefficient) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) :
    Differentiable ℂ (fun z => magneticPair c z S T u i f) :=
  (innerSL ℂ (FourierL2.embed (NewtonL2.conjugate f.val))).differentiable.comp
    (ComplexMagneticResponse.response_differentiable c S T u i)

theorem electricPair_real (c : Coefficient) (k S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    electricPair c k S T u i f = ∫ x, MaterialField.scattered c k u x i * f.val x :=
  ComplexExteriorResponse.real_test c k S T u hc i f hf

theorem magneticPair_actual (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    magneticPair c z S T u i f = ∫ x, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i * f.val x := by
  unfold magneticPair
  rw [← NewtonL2.scalar_pairing_inner]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp (ComplexMagneticResponse.response_actual c z S T u hc i)] with x hx
  by_cases hxb : x ∈ closedBall (0 : Space) T
  · rw [hx hxb]
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hxb (hf h))
    simp [hz]

def defectE (c : Coefficient) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) (z : ℂ) : ℂ :=
  electricPair c z S T u (next i) (testPartial (previous i) f) -
    electricPair c z S T u (previous i) (testPartial (next i) f) - I*z*magneticPair c z S T u i f

def defectH (c : Coefficient) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) (z : ℂ) : ℂ :=
  magneticPair c z S T u (next i) (testPartial (previous i) f) -
    magneticPair c z S T u (previous i) (testPartial (next i) f) + I*z*
      (electricPair c z S T u i f + ∫ x, DynamicVolume.source c u i x * f.val x)

theorem defectE_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2) (i : Fin 3) (f : Test) : Differentiable ℂ (defectE c S T u i f) := by
  unfold defectE
  exact ((electricPair_differentiable c S T hST u _ _).sub (electricPair_differentiable c S T hST u _ _)).sub
    (((differentiable_const I).mul differentiable_id).mul (magneticPair_differentiable c S T u i f))

theorem defectH_differentiable (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2) (i : Fin 3) (f : Test) : Differentiable ℂ (defectH c S T u i f) := by
  unfold defectH
  exact ((magneticPair_differentiable c S T u _ _).sub (magneticPair_differentiable c S T u _ _)).add
    (((differentiable_const I).mul differentiable_id).mul ((electricPair_differentiable c S T hST u i f).add (differentiable_const _)))

theorem real_zero (c : Coefficient) (S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) (k : ℝ) :
    defectE c S T u i f k = 0 ∧ defectH c S T u i f k = 0 := by
  have hs (j : Fin 3) : tsupport ((testPartial j f).val : Space → ℂ) ⊆ closedBall 0 T :=
    (partial_support j f).trans hf
  have hE := MagneticResponse.electric_curl_pairing k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (MaterialField.source_compact c u S hc) (StaticNewton.material_source_ae c u) i f
  have hH := MagneticResponse.magnetic_curl_pairing k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (MaterialField.source_compact c u S hc) (StaticNewton.material_source_ae c u) i f
  have hmag : ComplexMagneticLocal.magnetic (k : ℂ) (DynamicVolume.source c u) =
      MagneticResponse.magnetic k (DynamicVolume.source c u) := rfl
  constructor
  · unfold defectE
    rw [electricPair_real c k S T u hc _ _ (hs _), electricPair_real c k S T u hc _ _ (hs _),
      magneticPair_actual c k S T u hc i f hf]
    rw [hmag]
    dsimp only [MaterialField.scattered]
    linear_combination hE
  · unfold defectH
    rw [magneticPair_actual c k S T u hc _ _ (hs _), magneticPair_actual c k S T u hc _ _ (hs _),
      electricPair_real c k S T u hc i f hf]
    rw [hmag]
    dsimp only [MaterialField.scattered]
    linear_combination hH

theorem analytic_zero_of_real (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hreal : ∀ k : ℝ, F k = 0) (z : ℂ) : F z = 0 := by
  have hclosure : (1 : ℂ) ∈ closure ({w | F w = (0 : ℂ)} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1 + ε/2
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨hreal r, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ F Set.univ from fun w _ => hF.analyticAt w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => analyticAt_const) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem complex_zero (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) (z : ℂ) :
    defectE c S T u i f z = 0 ∧ defectH c S T u i f z = 0 := by
  constructor
  · exact analytic_zero_of_real _ (defectE_differentiable c S T hST u i f)
      (fun k => (real_zero c S T u hc i f hf k).1) z
  · exact analytic_zero_of_real _ (defectH_differentiable c S T hST u i f)
      (fun k => (real_zero c S T u hc i f hf k).2) z

theorem actual_maxwell (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) (z : ℂ) :
    ((∫ x, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) (next i) * (testPartial (previous i) f).val x) -
      (∫ x, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) (previous i) * (testPartial (next i) f).val x) =
        I*z * (∫ x, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i * f.val x)) ∧
    ((∫ x, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (next i) * (testPartial (previous i) f).val x) -
      (∫ x, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (previous i) * (testPartial (next i) f).val x) =
        -(I*z) * ((∫ x, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i * f.val x) +
          (∫ x, DynamicVolume.source c u i x * f.val x))) := by
  have hs (j : Fin 3) : tsupport ((testPartial j f).val : Space → ℂ) ⊆ closedBall 0 T :=
    (partial_support j f).trans hf
  obtain ⟨he,hh⟩ := complex_zero c S T hST u hc i f hf z
  unfold defectE at he
  unfold defectH at hh
  simp only [electricPair, testPair_integral] at he hh
  rw [magneticPair_actual c z S T u hc i f hf] at he
  rw [magneticPair_actual c z S T u hc _ _ (hs _), magneticPair_actual c z S T u hc _ _ (hs _)] at hh
  constructor
  · linear_combination he
  · linear_combination hh

#print axioms OQ14.ComplexMagneticMaxwell.actual_maxwell
#print axioms OQ14.ComplexMagneticMaxwell.complex_zero
#print axioms OQ14.ComplexMagneticMaxwell.real_zero
end OQ14.ComplexMagneticMaxwell





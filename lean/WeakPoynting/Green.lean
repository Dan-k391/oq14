import WeakPoynting

/-!
# Local Green identity for arbitrary weak H(curl) fields

The approximation input is the proved graph-norm smoothing theorem. All
pairings below are actual Lebesgue integrals of L2 products. No weak-field
product or integration-by-parts identity is postulated.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.WeakGreen

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
open scoped ComplexConjugate Topology

def scalarProduct (u : L2Scalar) : L2Scalar →L[ℂ] ℂ :=
  innerSL ℂ ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp u)

theorem scalarProduct_integrable (u v : L2Scalar) :
    Integrable (fun x => u x * v x) := by
  apply (L2.integrable_inner (𝕜 := ℂ)
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp u) v).congr
  filter_upwards [(Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp u] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

theorem scalarProduct_integral (u v : L2Scalar) :
    scalarProduct u v = ∫ x, u x * v x := by
  rw [scalarProduct, innerSL_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp u] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

def scaleL2 (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (u : L2Scalar) : L2Scalar :=
  ((Lp.memLp u).mul' (hf.memLp_of_hasCompactSupport hc : MemLp f ⊤ volume)).toLp
    (fun x => f x * u x)

theorem scaleL2_ae (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (u : L2Scalar) :
    (fun x => scaleL2 f hf hc u x) =ᵐ[volume] (fun x => f x * u x) :=
  ((Lp.memLp u).mul' (hf.memLp_of_hasCompactSupport hc : MemLp f ⊤ volume)).coeFn_toLp

def scale (χ : Test) (u : L2Scalar) : L2Scalar :=
  scaleL2 χ.function χ.regular.continuous χ.compact u

def dscale (χ : Test) (i : Fin 3) (u : L2Scalar) : L2Scalar :=
  scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
    (χ.compact.fderiv_apply ℝ (basis i)) u

theorem scalarProduct_scale_smooth (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u v : L2Scalar) (F : Space → ℂ) (hF : Continuous F)
    (hv : (fun x => v x) =ᵐ[volume] F) :
    scalarProduct (scaleL2 f hf hc u) v =
      testPair (fun x => f x * F x) (hf.mul hF) hc.mul_right u := by
  rw [scalarProduct_integral, testPair_integral]
  apply integral_congr_ae
  filter_upwards [scaleL2_ae f hf hc u, hv] with x hx hy
  rw [hx, hy]
  ring

def coordPair (a : L2Scalar) (j : Fin 3) : L2Vector →L[ℂ] ℂ :=
  (scalarProduct a).comp (ContinuousLinearMap.proj j)

def greenField (χ : Test) (E C : L2Vector) : L2Vector →L[ℂ] ℂ :=
  coordPair (scale χ (C 0)) 0 + coordPair (scale χ (C 1)) 1 + coordPair (scale χ (C 2)) 2 +
  coordPair (dscale χ 1 (E 2)) 0 - coordPair (dscale χ 2 (E 1)) 0 +
  coordPair (dscale χ 2 (E 0)) 1 - coordPair (dscale χ 0 (E 2)) 1 +
  coordPair (dscale χ 0 (E 1)) 2 - coordPair (dscale χ 1 (E 0)) 2

def greenCurl (χ : Test) (E : L2Vector) : L2Vector →L[ℂ] ℂ :=
  coordPair (scale χ (E 0)) 0 + coordPair (scale χ (E 1)) 1 + coordPair (scale χ (E 2)) 2

/-- The local Green residual, as an actual bounded functional of the second graph. -/
def greenFunctional (χ : Test) (u : HCurl) : Ambient →L[ℂ] ℂ :=
  (greenField χ u.val.1 u.val.2).comp (ContinuousLinearMap.fst ℂ L2Vector L2Vector) -
  (greenCurl χ u.val.1).comp (ContinuousLinearMap.snd ℂ L2Vector L2Vector)

def smoothProductTest (χ : Test) (F : Space → ℂ) (hF : ContDiff ℝ 1 F) : Test where
  function := fun x => χ.function x * F x
  regular := χ.regular.mul hF
  compact := χ.compact.mul_right

theorem derivativePair_smooth_product (χ : Test) (F : Space → ℂ)
    (hF : ContDiff ℝ 1 F) (u : L2Scalar) (i : Fin 3) :
    derivativePair (smoothProductTest χ F hF) i u =
      testPair (fun x => χ.function x * dcoord F x i)
        (χ.regular.continuous.mul (partial_continuous hF i)) χ.compact.mul_right u +
      testPair (fun x => dcoord χ.function x i * F x)
        ((partial_continuous χ.regular i).mul hF.continuous)
        (χ.compact.fderiv_apply ℝ (basis i)).mul_right u := by
  simp only [derivativePair, testPair_integral]
  rw [← integral_add
    (testPair_integrable _ (χ.regular.continuous.mul (partial_continuous hF i))
      χ.compact.mul_right u)
    (testPair_integrable _ ((partial_continuous χ.regular i).mul hF.continuous)
      (χ.compact.fderiv_apply ℝ (basis i)).mul_right u)]
  apply integral_congr_ae
  filter_upwards [] with x
  change u x * dcoord (fun y => χ.function y * F y) x i = _
  rw [partial_mul (χ.regular.differentiable (by norm_num) x)
    (hF.differentiable (by norm_num) x)]
  ring

theorem curl_component_continuous (F : Field)
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j)) (j : Fin 3) :
    Continuous (fun x => curl F x j) := by
  simpa only [curl_component, pd] using
    (partial_continuous (hF (previous j)) (next j)).sub
      (partial_continuous (hF (next j)) (previous j))

theorem testPair_curl_component (χ : Test) (F : Field)
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j)) (u : L2Scalar) (j : Fin 3) :
    testPair (fun x => χ.function x * curl F x j)
      (χ.regular.continuous.mul (curl_component_continuous F hF j)) χ.compact.mul_right u =
      testPair (fun x => χ.function x * dcoord (fun y => F y (previous j)) x (next j))
        (χ.regular.continuous.mul (partial_continuous (hF (previous j)) (next j)))
        χ.compact.mul_right u -
      testPair (fun x => χ.function x * dcoord (fun y => F y (next j)) x (previous j))
        (χ.regular.continuous.mul (partial_continuous (hF (next j)) (previous j)))
        χ.compact.mul_right u := by
  simp only [testPair_integral]
  rw [← integral_sub
    (testPair_integrable _ (χ.regular.continuous.mul
      (partial_continuous (hF (previous j)) (next j))) χ.compact.mul_right u)
    (testPair_integrable _ (χ.regular.continuous.mul
      (partial_continuous (hF (next j)) (previous j))) χ.compact.mul_right u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [curl_component]
  dsimp only [pd]
  ring

theorem green_smooth_right (χ : Test) (u v : HCurl) (hv : SmoothGraph v) :
    greenFunctional χ u v.val = 0 := by
  obtain ⟨F, hF, hEF, hCF⟩ := hv
  have hF1 (j : Fin 3) : ContDiff ℝ 1 (fun x => F x j) := (hF j).of_le (by simp)
  have hw (j : Fin 3) := u.property (smoothProductTest χ (fun x => F x j) (hF1 j)) j
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  change weakCurl (smoothProductTest χ (fun x => F x 0) (hF1 0)) 0 u.val.1 -
    valuePair (smoothProductTest χ (fun x => F x 0) (hF1 0)) (u.val.2 0) = 0 at h0
  change weakCurl (smoothProductTest χ (fun x => F x 1) (hF1 1)) 1 u.val.1 -
    valuePair (smoothProductTest χ (fun x => F x 1) (hF1 1)) (u.val.2 1) = 0 at h1
  change weakCurl (smoothProductTest χ (fun x => F x 2) (hF1 2)) 2 u.val.1 -
    valuePair (smoothProductTest χ (fun x => F x 2) (hF1 2)) (u.val.2 2) = 0 at h2
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, derivativePair_smooth_product, valuePair,
    next, previous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  dsimp only [smoothProductTest] at h0 h1 h2
  have hs (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
      (a : L2Scalar) (j : Fin 3) :
      scalarProduct (scaleL2 f hf hc a) (v.val.1 j) =
        testPair (fun x => f x * F x j) (hf.mul (hF j).continuous) hc.mul_right a :=
    scalarProduct_scale_smooth f hf hc a _ _ (hF j).continuous (hEF j)
  have ht (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
      (a : L2Scalar) (j : Fin 3) :
      scalarProduct (scaleL2 f hf hc a) (v.val.2 j) =
        testPair (fun x => f x * curl F x j)
          (hf.mul (curl_component_continuous F hF1 j)) hc.mul_right a :=
    scalarProduct_scale_smooth f hf hc a _ _ (curl_component_continuous F hF1 j) (hCF j)
  simp only [greenFunctional, greenField, greenCurl, coordPair, scale, dscale,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hs, ht]
  rw [testPair_curl_component χ F hF1 _ 0, testPair_curl_component χ F hF1 _ 1,
    testPair_curl_component χ F hF1 _ 2]
  simp only [next, previous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination -h0 - h1 - h2

/-- The genuine local integration-by-parts law for two arbitrary H(curl) fields. -/
theorem weak_green_functional_zero (χ : Test) (u v : HCurl) :
    greenFunctional χ u v.val = 0 := by
  obtain ⟨vseq, hs, hv⟩ := smooth_graph_approximation v
  have hlim := ((greenFunctional χ u).continuous.comp continuous_subtype_val).tendsto v
  have hh := hlim.comp hv
  have hz : Filter.Tendsto (fun n => greenFunctional χ u (vseq n).val)
      Filter.atTop (𝓝 (0 : ℂ)) := by
    have heq : (fun n => greenFunctional χ u (vseq n).val) = fun _ : ℕ => (0 : ℂ) := by
      funext n
      exact green_smooth_right χ u (vseq n) (hs n)
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hh hz

theorem scalarProduct_scale_integral (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u v : L2Scalar) :
    scalarProduct (scaleL2 f hf hc u) v = ∫ x, f x * u x * v x := by
  rw [scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [scaleL2_ae f hf hc u] with x hx
  rw [hx]

/-- Expanded integral of χ(C·F−E·D) + grad χ·(E×F), with C=curl E and D=curl F. -/
def localGreenIntegral (χ : Test) (E C F D : L2Vector) : ℂ :=
  (∫ x, χ.function x * C 0 x * F 0 x) +
  (∫ x, χ.function x * C 1 x * F 1 x) +
  (∫ x, χ.function x * C 2 x * F 2 x) +
  (∫ x, dcoord χ.function x 1 * E 2 x * F 0 x) -
  (∫ x, dcoord χ.function x 2 * E 1 x * F 0 x) +
  (∫ x, dcoord χ.function x 2 * E 0 x * F 1 x) -
  (∫ x, dcoord χ.function x 0 * E 2 x * F 1 x) +
  (∫ x, dcoord χ.function x 0 * E 1 x * F 2 x) -
  (∫ x, dcoord χ.function x 1 * E 0 x * F 2 x) -
  ((∫ x, χ.function x * E 0 x * D 0 x) +
   (∫ x, χ.function x * E 1 x * D 1 x) +
   (∫ x, χ.function x * E 2 x * D 2 x))

theorem greenFunctional_integral (χ : Test) (u v : HCurl) :
    greenFunctional χ u v.val = localGreenIntegral χ u.val.1 u.val.2 v.val.1 v.val.2 := by
  simp only [greenFunctional, greenField, greenCurl, coordPair, scale, dscale,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    scalarProduct_scale_integral, localGreenIntegral]

/-- A local weak cross-product/Green identity stated entirely as Lebesgue integrals. -/
theorem weak_local_Green (χ : Test) (u v : HCurl) :
    localGreenIntegral χ u.val.1 u.val.2 v.val.1 v.val.2 = 0 := by
  rw [← greenFunctional_integral]
  exact weak_green_functional_zero χ u v

end OQ14.WeakGreen

#print axioms OQ14.WeakGreen.scalarProduct_integrable
#print axioms OQ14.WeakGreen.scalarProduct_integral
#print axioms OQ14.WeakGreen.green_smooth_right
#print axioms OQ14.WeakGreen.weak_green_functional_zero
#print axioms OQ14.WeakGreen.greenFunctional_integral
#print axioms OQ14.WeakGreen.weak_local_Green

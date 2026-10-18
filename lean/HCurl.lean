import Maxwell
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The actual distributional curl graph in L2 on Euclidean three-space

Coordinate L2 classes and compactly supported C1 test functions are used.
The weak curl relation is an equality of genuine Lebesgue integrals.
Closedness is proved from bounded L2 test pairings, not postulated.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.WeakCurl

open MeasureTheory OQ14.Maxwell
open scoped ComplexConjugate Topology

abbrev L2Scalar := Lp ℂ 2 (volume : Measure Space)
abbrev L2Vector := Fin 3 → L2Scalar
abbrev Ambient := L2Vector × L2Vector

structure Test where
  function : Space → ℂ
  regular : ContDiff ℝ 1 function
  compact : HasCompactSupport function

theorem conjugate_test_memLp (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    MemLp (fun x => conj (f x)) 2 (volume : Measure Space) :=
  (Complex.continuous_conj.comp hf).memLp_of_hasCompactSupport
    (hc.comp_left (map_zero (starRingEnd ℂ)))

/-- The bilinear L2 pairing with a compact continuous function, represented
as a bounded linear functional using the genuine L2 inner product. -/
def testPair (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    L2Scalar →L[ℂ] ℂ :=
  innerSL ℂ ((conjugate_test_memLp f hf hc).toLp (fun x => conj (f x)))

theorem testPair_integrable (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar) :
    Integrable (fun x => u x * f x) := by
  have hh := L2.integrable_inner (𝕜 := ℂ)
    ((conjugate_test_memLp f hf hc).toLp (fun x => conj (f x))) u
  apply hh.congr
  filter_upwards [(conjugate_test_memLp f hf hc).coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

theorem testPair_integral (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar) :
    testPair f hf hc u = ∫ x, u x * f x := by
  rw [testPair, innerSL_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(conjugate_test_memLp f hf hc).coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

def valuePair (φ : Test) : L2Scalar →L[ℂ] ℂ :=
  testPair φ.function φ.regular.continuous φ.compact

def derivativePair (φ : Test) (i : Fin 3) : L2Scalar →L[ℂ] ℂ :=
  testPair (fun x => dcoord φ.function x i) (partial_continuous φ.regular i)
    (φ.compact.fderiv_apply ℝ (basis i))

def next (j : Fin 3) : Fin 3 := ![1, 2, 0] j
def previous (j : Fin 3) : Fin 3 := ![2, 0, 1] j

/-- Pair the distributional curl's j-th component with a scalar test. -/
def weakCurl (φ : Test) (j : Fin 3) : L2Vector →L[ℂ] ℂ :=
  (derivativePair φ (previous j)).comp (ContinuousLinearMap.proj (next j)) -
  (derivativePair φ (next j)).comp (ContinuousLinearMap.proj (previous j))

def residual (φ : Test) (j : Fin 3) : Ambient →L[ℂ] ℂ :=
  (weakCurl φ j).comp (ContinuousLinearMap.fst ℂ L2Vector L2Vector) -
  ((valuePair φ).comp (ContinuousLinearMap.proj j)).comp
    (ContinuousLinearMap.snd ℂ L2Vector L2Vector)

/-- This predicate is the distributional curl relation, with actual L2
classes and bounded test functionals. Its integral meaning is proved below. -/
def HasWeakCurl (E C : L2Vector) : Prop := ∀ φ j, residual φ j (E, C) = 0

theorem weakCurl_integral (φ : Test) (j : Fin 3) (E : L2Vector) :
    weakCurl φ j E =
      (∫ x, E (next j) x * dcoord φ.function x (previous j)) -
      (∫ x, E (previous j) x * dcoord φ.function x (next j)) := by
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, derivativePair, testPair_integral]

theorem hasWeakCurl_iff_integral (E C : L2Vector) :
    HasWeakCurl E C ↔ ∀ φ : Test, ∀ j : Fin 3,
      (∫ x, C j x * φ.function x) =
      (∫ x, E (next j) x * dcoord φ.function x (previous j)) -
      (∫ x, E (previous j) x * dcoord φ.function x (next j)) := by
  constructor
  · intro h φ j
    have hh := h φ j
    change weakCurl φ j E - valuePair φ (C j) = 0 at hh
    rw [weakCurl_integral, valuePair, testPair_integral] at hh
    exact (sub_eq_zero.mp hh).symm
  · intro h φ j
    change weakCurl φ j E - valuePair φ (C j) = 0
    rw [weakCurl_integral, valuePair, testPair_integral]
    exact sub_eq_zero.mpr (h φ j).symm

/-- H(curl), represented by its graph (field, distributional curl). -/
def graph : Submodule ℂ Ambient where
  carrier := {u | HasWeakCurl u.1 u.2}
  zero_mem' := by intro φ j; exact map_zero (residual φ j)
  add_mem' := by
    intro u v hu hv φ j
    change residual φ j (u + v) = 0
    rw [map_add, hu φ j, hv φ j, add_zero]
  smul_mem' := by
    intro a u hu φ j
    change residual φ j (a • u) = 0
    rw [map_smul, hu φ j, smul_zero]

theorem graph_closed : IsClosed (graph : Set Ambient) := by
  have hset : (graph : Set Ambient) = ⋂ φ : Test, ⋂ j : Fin 3,
      (LinearMap.ker (residual φ j).toLinearMap : Set Ambient) := by
    ext u
    simp [graph, HasWeakCurl]
  rw [hset]
  exact isClosed_iInter (fun φ => isClosed_iInter
    (fun j => ContinuousLinearMap.isClosed_ker (residual φ j)))

abbrev HCurl := graph

instance : CompleteSpace HCurl := graph_closed.completeSpace_coe

/-- A closed distributional graph is a genuine complete normed space. -/
theorem hcurl_complete : CompleteSpace HCurl := inferInstance

theorem graph_norm (u : HCurl) : ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖ := rfl

/-- Passing to simultaneous L2 limits preserves the distributional curl. -/
theorem weakCurl_limit {E C : ℕ → L2Vector} {e c : L2Vector}
    (h : ∀ n, HasWeakCurl (E n) (C n))
    (hE : Filter.Tendsto E Filter.atTop (𝓝 e))
    (hC : Filter.Tendsto C Filter.atTop (𝓝 c)) : HasWeakCurl e c := by
  exact graph_closed.mem_of_tendsto (hE.prodMk_nhds hC) (Filter.Eventually.of_forall h)

def fieldToL2 (F : Field) (hF : ∀ j, MemLp (fun x => F x j) 2
    (volume : Measure Space)) : L2Vector := fun j => (hF j).toLp (fun x => F x j)

theorem fieldToL2_integral (F : Field)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (volume : Measure Space))
    (f : Space → ℂ) (j : Fin 3) :
    (∫ x, fieldToL2 F hF j x * f x) = ∫ x, F x j * f x := by
  apply integral_congr_ae
  filter_upwards [(hF j).coeFn_toLp] with x hx
  exact congrArg (fun z => z * f x) hx

/-- Classical fields whose field and actual curl are L2 belong to the
distributional graph. The curl formula is derived by integration by parts. -/
theorem classical_hasWeakCurl (F : Field)
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j))
    (hE : ∀ j, MemLp (fun x => F x j) 2 (volume : Measure Space))
    (hC : ∀ j, MemLp (fun x => curl F x j) 2 (volume : Measure Space)) :
    HasWeakCurl (fieldToL2 F hE) (fieldToL2 (curl F) hC) := by
  rw [hasWeakCurl_iff_integral]
  intro φ j
  simp only [fieldToL2_integral]
  have hh := congrFun (curl_integration_by_parts F hF φ.regular φ.compact) j
  fin_cases j <;> simpa [next, previous, weakCurlPairing] using hh

/-- A scalar L2 class is determined by all compact C1 test pairings. The
proof uses the genuine fundamental lemma for locally integrable functions. -/
theorem tests_separate (u v : L2Scalar)
    (h : ∀ φ : Test, valuePair φ u = valuePair φ v) : u = v := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num))
    ((Lp.memLp v).locallyIntegrable (by norm_num))
  intro g hg hc
  let φ : Test := {
    function := fun x => (g x : ℂ)
    regular := Complex.ofRealCLM.contDiff.comp (hg.of_le (by simp))
    compact := hc.comp_left (g := fun a : ℝ => (a : ℂ)) (by simp)
  }
  have hh := h φ
  simp only [valuePair, testPair_integral] at hh
  simpa [φ, Complex.real_smul, mul_comm] using hh

theorem weakCurl_unique {E C D : L2Vector}
    (hC : HasWeakCurl E C) (hD : HasWeakCurl E D) : C = D := by
  funext j
  apply tests_separate
  intro φ
  have hc := hC φ j
  have hd := hD φ j
  change weakCurl φ j E - valuePair φ (C j) = 0 at hc
  change weakCurl φ j E - valuePair φ (D j) = 0 at hd
  exact (sub_eq_zero.mp hc).symm.trans (sub_eq_zero.mp hd)

/-- The field projection is injective: the graph representation stores no
extra unconstrained curl data. -/
theorem field_projection_injective :
    Function.Injective (fun u : HCurl => u.val.1) := by
  intro u v h
  change u.val.1 = v.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply weakCurl_unique u.property
  rw [h]
  exact v.property

end OQ14.WeakCurl

#print axioms OQ14.WeakCurl.testPair_integral
#print axioms OQ14.WeakCurl.testPair_integrable
#print axioms OQ14.WeakCurl.hasWeakCurl_iff_integral
#print axioms OQ14.WeakCurl.graph_closed
#print axioms OQ14.WeakCurl.hcurl_complete
#print axioms OQ14.WeakCurl.graph_norm
#print axioms OQ14.WeakCurl.weakCurl_limit
#print axioms OQ14.WeakCurl.classical_hasWeakCurl
#print axioms OQ14.WeakCurl.tests_separate
#print axioms OQ14.WeakCurl.weakCurl_unique
#print axioms OQ14.WeakCurl.field_projection_injective

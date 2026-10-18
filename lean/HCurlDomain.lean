import HCurl

/-!
# Distributional curl on open subsets of Euclidean three-space

The field and curl are L2 equivalence classes for restricted Lebesgue measure.
Tests have compact support inside the region. In particular no global L2
condition, zero boundary condition, or boundary trace is imposed on a field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.DomainCurl

open MeasureTheory OQ14.Maxwell
open scoped ComplexConjugate Topology

variable (Ω : Set Space)

abbrev regionMeasure : Measure Space := volume.restrict Ω
abbrev L2Scalar := Lp ℂ 2 (regionMeasure Ω)
abbrev L2Vector := Fin 3 → L2Scalar Ω
abbrev Ambient := L2Vector Ω × L2Vector Ω

structure Test extends WeakCurl.Test where
  inside : tsupport function ⊆ Ω

theorem conjugate_test_memLp (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    MemLp (fun x => conj (f x)) 2 (regionMeasure Ω) :=
  (Complex.continuous_conj.comp hf).memLp_of_hasCompactSupport
    (hc.comp_left (map_zero (starRingEnd ℂ)))

def testPair (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    L2Scalar Ω →L[ℂ] ℂ :=
  innerSL ℂ ((conjugate_test_memLp Ω f hf hc).toLp (fun x => conj (f x)))

theorem testPair_integrable (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) :
    Integrable (fun x => u x * f x) (regionMeasure Ω) := by
  have hh := L2.integrable_inner (𝕜 := ℂ)
    ((conjugate_test_memLp Ω f hf hc).toLp (fun x => conj (f x))) u
  apply hh.congr
  filter_upwards [(conjugate_test_memLp Ω f hf hc).coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

theorem testPair_integral (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) :
    testPair Ω f hf hc u = ∫ x in Ω, u x * f x := by
  rw [testPair, innerSL_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(conjugate_test_memLp Ω f hf hc).coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

def valuePair (φ : Test Ω) : L2Scalar Ω →L[ℂ] ℂ :=
  testPair Ω φ.function φ.regular.continuous φ.compact

def derivativePair (φ : Test Ω) (i : Fin 3) : L2Scalar Ω →L[ℂ] ℂ :=
  testPair Ω (fun x => dcoord φ.function x i) (partial_continuous φ.regular i)
    (φ.compact.fderiv_apply ℝ (basis i))

def weakCurl (φ : Test Ω) (j : Fin 3) : L2Vector Ω →L[ℂ] ℂ :=
  (derivativePair Ω φ (WeakCurl.previous j)).comp
      (ContinuousLinearMap.proj (WeakCurl.next j)) -
  (derivativePair Ω φ (WeakCurl.next j)).comp
      (ContinuousLinearMap.proj (WeakCurl.previous j))

def residual (φ : Test Ω) (j : Fin 3) : Ambient Ω →L[ℂ] ℂ :=
  (weakCurl Ω φ j).comp (ContinuousLinearMap.fst ℂ (L2Vector Ω) (L2Vector Ω)) -
  ((valuePair Ω φ).comp (ContinuousLinearMap.proj j)).comp
    (ContinuousLinearMap.snd ℂ (L2Vector Ω) (L2Vector Ω))

def HasWeakCurl (E C : L2Vector Ω) : Prop :=
  ∀ φ j, residual Ω φ j (E, C) = 0

theorem weakCurl_integral (φ : Test Ω) (j : Fin 3) (E : L2Vector Ω) :
    weakCurl Ω φ j E =
      (∫ x in Ω, E (WeakCurl.next j) x *
        dcoord φ.function x (WeakCurl.previous j)) -
      (∫ x in Ω, E (WeakCurl.previous j) x *
        dcoord φ.function x (WeakCurl.next j)) := by
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, derivativePair, testPair_integral]

theorem hasWeakCurl_iff_integral (E C : L2Vector Ω) :
    HasWeakCurl Ω E C ↔ ∀ φ : Test Ω, ∀ j : Fin 3,
      (∫ x in Ω, C j x * φ.function x) =
      (∫ x in Ω, E (WeakCurl.next j) x *
        dcoord φ.function x (WeakCurl.previous j)) -
      (∫ x in Ω, E (WeakCurl.previous j) x *
        dcoord φ.function x (WeakCurl.next j)) := by
  constructor
  · intro h φ j
    have hh := h φ j
    change weakCurl Ω φ j E - valuePair Ω φ (C j) = 0 at hh
    rw [weakCurl_integral, valuePair, testPair_integral] at hh
    exact (sub_eq_zero.mp hh).symm
  · intro h φ j
    change weakCurl Ω φ j E - valuePair Ω φ (C j) = 0
    rw [weakCurl_integral, valuePair, testPair_integral]
    exact sub_eq_zero.mpr (h φ j).symm

def graph : Submodule ℂ (Ambient Ω) where
  carrier := {u | HasWeakCurl Ω u.1 u.2}
  zero_mem' := by intro φ j; exact map_zero (residual Ω φ j)
  add_mem' := by
    intro u v hu hv φ j
    change residual Ω φ j (u + v) = 0
    rw [map_add, hu φ j, hv φ j, add_zero]
  smul_mem' := by
    intro a u hu φ j
    change residual Ω φ j (a • u) = 0
    rw [map_smul, hu φ j, smul_zero]

theorem graph_closed : IsClosed (graph Ω : Set (Ambient Ω)) := by
  have hset : (graph Ω : Set (Ambient Ω)) = ⋂ φ : Test Ω, ⋂ j : Fin 3,
      (LinearMap.ker (residual Ω φ j).toLinearMap : Set (Ambient Ω)) := by
    ext u
    simp [graph, HasWeakCurl]
  rw [hset]
  exact isClosed_iInter (fun φ => isClosed_iInter
    (fun j => ContinuousLinearMap.isClosed_ker (residual Ω φ j)))

abbrev HCurl := graph Ω

instance : CompleteSpace (HCurl Ω) := (graph_closed Ω).completeSpace_coe

theorem hcurl_complete : CompleteSpace (HCurl Ω) := inferInstance

theorem graph_norm (u : HCurl Ω) : ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖ := rfl

theorem weakCurl_limit {E C : ℕ → L2Vector Ω} {e c : L2Vector Ω}
    (h : ∀ n, HasWeakCurl Ω (E n) (C n))
    (hE : Filter.Tendsto E Filter.atTop (𝓝 e))
    (hC : Filter.Tendsto C Filter.atTop (𝓝 c)) : HasWeakCurl Ω e c := by
  have hmem : ∀ n, (E n, C n) ∈ (graph Ω : Set (Ambient Ω)) := h
  change (e, c) ∈ (graph Ω : Set (Ambient Ω))
  exact (graph_closed Ω).mem_of_tendsto (hE.prodMk_nhds hC)
    (Filter.Eventually.of_forall hmem)

/-- Tests supported inside an open region separate its actual L2 classes. -/
theorem tests_separate (hΩ : IsOpen Ω) (u v : L2Scalar Ω)
    (h : ∀ φ : Test Ω, valuePair Ω φ u = valuePair Ω φ v) : u = v := by
  apply Lp.ext
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv := (Lp.memLp v).locallyIntegrable (by norm_num)
  have hz : ∀ᵐ x ∂regionMeasure Ω, x ∈ Ω → u x - v x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hu.sub hv).locallyIntegrableOn Ω)
    intro g hg hc hi
    let φ : Test Ω := {
      function := fun x => (g x : ℂ)
      regular := Complex.ofRealCLM.contDiff.comp (hg.of_le (by simp))
      compact := hc.comp_left (g := fun a : ℝ => (a : ℂ)) (by simp)
      inside := by
        have hs : Function.support (fun x => (g x : ℂ)) = Function.support g := by
          ext x
          simp [Function.mem_support]
        simpa only [tsupport, hs] using hi
    }
    have hh := h φ
    simp only [valuePair, testPair_integral] at hh
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub
      (hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc)
      (hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc)]
    apply sub_eq_zero.mpr
    simpa [φ, Complex.real_smul, mul_comm] using hh
  filter_upwards [hz, ae_restrict_mem hΩ.measurableSet] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

theorem weakCurl_unique (hΩ : IsOpen Ω) {E C D : L2Vector Ω}
    (hC : HasWeakCurl Ω E C) (hD : HasWeakCurl Ω E D) : C = D := by
  funext j
  apply tests_separate Ω hΩ
  intro φ
  have hc := hC φ j
  have hd := hD φ j
  change weakCurl Ω φ j E - valuePair Ω φ (C j) = 0 at hc
  change weakCurl Ω φ j E - valuePair Ω φ (D j) = 0 at hd
  exact (sub_eq_zero.mp hc).symm.trans (sub_eq_zero.mp hd)

theorem field_projection_injective (hΩ : IsOpen Ω) :
    Function.Injective (fun u : HCurl Ω => u.val.1) := by
  intro u v h
  change u.val.1 = v.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply weakCurl_unique Ω hΩ u.property
  rw [h]
  exact v.property

def fieldToL2 (F : Field)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (regionMeasure Ω)) : L2Vector Ω :=
  fun j => (hF j).toLp (fun x => F x j)

theorem fieldToL2_integral (F : Field)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (regionMeasure Ω))
    (f : Space → ℂ) (j : Fin 3) :
    (∫ x in Ω, fieldToL2 Ω F hF j x * f x) = ∫ x in Ω, F x j * f x := by
  apply integral_congr_ae
  filter_upwards [(hF j).coeFn_toLp] with x hx
  exact congrArg (fun z => z * f x) hx

theorem test_zero_outside (φ : Test Ω) {x : Space} (hx : x ∉ Ω) :
    φ.function x = 0 := by
  by_contra hn
  exact hx (φ.inside (subset_closure hn))

theorem derivative_test_zero_outside (φ : Test Ω) (i : Fin 3)
    {x : Space} (hx : x ∉ Ω) : dcoord φ.function x i = 0 := by
  have hn : x ∉ tsupport φ.function := fun hm => hx (φ.inside hm)
  simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]

/-- C1 fields with region-L2 field and curl belong to H(curl) on the region.
Their behavior outside the region is not required to be square integrable. -/
theorem classical_hasWeakCurl (F : Field)
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j))
    (hE : ∀ j, MemLp (fun x => F x j) 2 (regionMeasure Ω))
    (hC : ∀ j, MemLp (fun x => curl F x j) 2 (regionMeasure Ω)) :
    HasWeakCurl Ω (fieldToL2 Ω F hE) (fieldToL2 Ω (curl F) hC) := by
  rw [hasWeakCurl_iff_integral]
  intro φ j
  simp only [fieldToL2_integral]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [test_zero_outside Ω φ hx, mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [derivative_test_zero_outside Ω φ _ hx, mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [derivative_test_zero_outside Ω φ _ hx, mul_zero])]
  have hh := congrFun (curl_integration_by_parts F hF φ.regular φ.compact) j
  fin_cases j <;> simpa [WeakCurl.next, WeakCurl.previous, weakCurlPairing] using hh

/-- A compact C2 test has admissible C1 coordinate derivative tests. -/
def derivativeTest (f : Space → ℂ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hi : tsupport f ⊆ Ω) (i : Fin 3) : Test Ω where
  function := fun x => dcoord f x i
  regular := by
    have hd : ContDiff ℝ 1 (fderiv ℝ f) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
    exact hd.clm_apply contDiff_const
  compact := hc.fderiv_apply ℝ (basis i)
  inside := by
    apply Set.Subset.trans _ hi
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    have hz : dcoord f x i = 0 := by simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
    exact hx hz

/-- The distributional divergence vanishes, tested against compact C2 scalars.
This test class contains all compact smooth distribution tests. -/
def DivergenceFree (C : L2Vector Ω) : Prop :=
  ∀ (f : Space → ℂ), ContDiff ℝ 2 f → HasCompactSupport f → tsupport f ⊆ Ω →
    (∫ x in Ω, C 0 x * dcoord f x 0) +
    (∫ x in Ω, C 1 x * dcoord f x 1) +
    (∫ x in Ω, C 2 x * dcoord f x 2) = 0

/-- The curl of an arbitrary weak L2 field has zero distributional divergence.
No differentiability of the field or of its weak curl is assumed. -/
theorem weak_divergence_curl {E C : L2Vector Ω}
    (h : HasWeakCurl Ω E C) : DivergenceFree Ω C := by
  intro f hf hc hi
  have h0 := (hasWeakCurl_iff_integral Ω E C).mp h (derivativeTest Ω f hf hc hi 0) 0
  have h1 := (hasWeakCurl_iff_integral Ω E C).mp h (derivativeTest Ω f hf hc hi 1) 1
  have h2 := (hasWeakCurl_iff_integral Ω E C).mp h (derivativeTest Ω f hf hc hi 2) 2
  simp only [derivativeTest, WeakCurl.next, WeakCurl.previous, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [h0, h1, h2]
  simp_rw [partial_comm hf _ 2 0, partial_comm hf _ 1 0, partial_comm hf _ 2 1]
  ring

end OQ14.DomainCurl

#print axioms OQ14.DomainCurl.testPair_integrable
#print axioms OQ14.DomainCurl.testPair_integral
#print axioms OQ14.DomainCurl.hasWeakCurl_iff_integral
#print axioms OQ14.DomainCurl.graph_closed
#print axioms OQ14.DomainCurl.hcurl_complete
#print axioms OQ14.DomainCurl.graph_norm
#print axioms OQ14.DomainCurl.weakCurl_limit
#print axioms OQ14.DomainCurl.tests_separate
#print axioms OQ14.DomainCurl.weakCurl_unique
#print axioms OQ14.DomainCurl.field_projection_injective
#print axioms OQ14.DomainCurl.classical_hasWeakCurl
#print axioms OQ14.DomainCurl.weak_divergence_curl

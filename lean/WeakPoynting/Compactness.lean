import WeakPoynting.Translations
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Actual compactness for compactly supported weak H1 fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.WeakCompactness

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.WeakTranslations Filter
open scoped Topology

/-- Essential support of the actual L2 equivalence class. -/
def SupportedIn (u : L2Scalar) (K : Set Space) : Prop :=
  ∀ᵐ x, x ∉ K → u x = 0

theorem supported_compact {u : L2Scalar} {K : Set Space}
    (hK : IsCompact K) (hu : SupportedIn u K) : CompactRepresentative u := by
  classical
  refine ⟨K.indicator u, HasCompactSupport.intro hK ?_, ?_⟩
  · intro x hx
    exact Set.indicator_of_not_mem hx _
  · filter_upwards [hu] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]

def kernelDerivative (φ : ContDiffBump (0 : Space)) (i : Fin 3) : Test where
  function := fun x => dcoord (complexKernel φ) x i
  regular := by
    have h2 : ContDiff ℝ 2 (complexKernel φ) :=
      (complexKernel_regular φ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hd : ContDiff ℝ 1 (fderiv ℝ (complexKernel φ)) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp h2 |>.2.2
    exact hd.clm_apply contDiff_const
  compact := (complexKernel_compact φ).fderiv_apply ℝ (basis i)

theorem smoothScalar_global_difference (φ : ContDiffBump (0 : Space))
    (u : L2Scalar) (a b : Space) :
    ‖smoothScalar (complexKernel φ) u a - smoothScalar (complexKernel φ) u b‖ ≤
      (‖u‖ * ∑ i, ‖testL2 (kernelDerivative φ i)‖) * ‖a - b‖ := by
  have hd (x : Space) : ‖fderiv ℝ (smoothScalar (complexKernel φ) u) x‖ ≤
      ‖u‖ * ∑ i, ‖testL2 (kernelDerivative φ i)‖ := by
    apply (coordinate_opNorm_le _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ‖dcoord (smoothScalar (kernelTest φ).function u) x i‖ ≤ _
    rw [smoothScalar_partial]
    exact smoothScalar_norm_le (kernelDerivative φ i) u x
  exact (convex_univ : Convex ℝ (Set.univ : Set Space)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (smoothScalar_regular (complexKernel_regular φ)
      (complexKernel_compact φ) u).differentiable (by simp) x)
    (fun x _ => hd x) (Set.mem_univ b) (Set.mem_univ a)

theorem mollified_zero_outside (φ : ContDiffBump (0 : Space)) {u : L2Scalar}
    {R : ℝ} (hu : SupportedIn u (Metric.closedBall 0 R)) {x : Space}
    (hx : R + φ.rOut < ‖x‖) : smoothScalar (complexKernel φ) u x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hu] with y hy
  by_cases h : y ∈ Metric.closedBall (0 : Space) R
  · have hn : φ.rOut < ‖x - y‖ := by
      have hY : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using h
      have ht := norm_add_le (x - y) y
      rw [sub_add_cancel] at ht
      linarith
    have hz : φ.normed volume (x - y) = 0 := by
      have hs : x - y ∉ Function.support (φ.normed (volume : Measure Space)) := by
        rw [φ.support_normed_eq]
        simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hn.le
      simpa only [Function.mem_support, not_not] using hs
    simp [complexKernel, hz]
  · simp [hy h]

def mollifiedRestriction (φ : ContDiffBump (0 : Space)) (u : L2Scalar) (S : ℝ) :
    BoundedContinuousFunction (Metric.closedBall (0 : Space) S) ℂ := by
  letI : CompactSpace (Metric.closedBall (0 : Space) S) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => smoothScalar (complexKernel φ) u x,
      (smoothScalar_regular (complexKernel_regular φ) (complexKernel_compact φ) u).continuous.comp
        continuous_subtype_val⟩

theorem mollified_restrictions_precompact (φ : ContDiffBump (0 : Space))
    (S M : ℝ) (_hM : 0 ≤ M) :
    IsCompact (closure (Set.range (fun u : {u : L2Scalar // ‖u‖ ≤ M} =>
      mollifiedRestriction φ u.val S))) := by
  letI : CompactSpace (Metric.closedBall (0 : Space) S) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let A := Set.range (fun u : {u : L2Scalar // ‖u‖ ≤ M} =>
    mollifiedRestriction φ u.val S)
  apply BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℂ) (M * ‖testL2 (kernelTest φ)‖)) (isCompact_closedBall _ _) A
  · intro f x hf
    obtain ⟨u, rfl⟩ := hf
    change ‖smoothScalar (complexKernel φ) u.val x.val - 0‖ ≤ _
    rw [sub_zero]
    exact (smoothScalar_norm_le (kernelTest φ) u.val x.val).trans
      (mul_le_mul_of_nonneg_right u.property (norm_nonneg _))
  · let L := M * ∑ i, ‖testL2 (kernelDerivative φ i)‖
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => L * r)
      (by simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto
        (fun r : ℝ => L * r) (𝓝 0) (𝓝 (L * 0))))
    intro x y f
    obtain ⟨u, hu⟩ := f.property
    rw [← hu]
    change ‖smoothScalar (complexKernel φ) u.val x.val -
      smoothScalar (complexKernel φ) u.val y.val‖ ≤ L * dist x y
    apply (smoothScalar_global_difference φ u.val x.val y.val).trans
    change _ ≤ (M * ∑ i, ‖testL2 (kernelDerivative φ i)‖) * ‖x.val - y.val‖
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right u.property (by positivity)) (norm_nonneg _)

def ballIndicator (S : ℝ) : L2Scalar :=
  indicatorConstLp 2 measurableSet_closedBall
    (isCompact_closedBall (0 : Space) S).measure_lt_top.ne (1 : ℂ)

theorem mollified_L2_distance (φ : ContDiffBump (0 : Space)) {R : ℝ}
    {u v : L2Scalar} (hu : SupportedIn u (Metric.closedBall 0 R))
    (hv : SupportedIn v (Metric.closedBall 0 R)) :
    dist (mollifyL2 φ u) (mollifyL2 φ v) ≤
      ‖ballIndicator (R + φ.rOut)‖ *
        dist (mollifiedRestriction φ u (R + φ.rOut))
          (mollifiedRestriction φ v (R + φ.rOut)) := by
  rw [dist_eq_norm, mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (mollifyL2 φ u) (mollifyL2 φ v),
    (smoothScalar_memLp φ u).coeFn_toLp, (smoothScalar_memLp φ v).coeFn_toLp,
    indicatorConstLp_coeFn (p := (2 : ENNReal))
      (hs := measurableSet_closedBall)
      (hμs := (isCompact_closedBall (0 : Space) (R + φ.rOut)).measure_lt_top.ne)
      (c := (1 : ℂ))] with x hx hxu hxv hxi
  rw [hx]
  simp only [Pi.sub_apply]
  change mollifyL2 φ u x = smoothScalar (complexKernel φ) u x at hxu
  change mollifyL2 φ v x = smoothScalar (complexKernel φ) v x at hxv
  rw [hxu, hxv]
  by_cases h : x ∈ Metric.closedBall (0 : Space) (R + φ.rOut)
  · have hi : ballIndicator (R + φ.rOut) x = 1 :=
      hxi.trans (Set.indicator_of_mem h _)
    rw [hi, norm_one, mul_one]
    exact BoundedContinuousFunction.dist_coe_le_dist
      (f := mollifiedRestriction φ u (R + φ.rOut))
      (g := mollifiedRestriction φ v (R + φ.rOut))
      (⟨x, h⟩ : Metric.closedBall (0 : Space) (R + φ.rOut))
  · have hn : R + φ.rOut < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h
    rw [mollified_zero_outside φ hu hn, mollified_zero_outside φ hv hn]
    simp only [sub_zero, norm_zero]
    positivity

/-- A metric transfer lemma proved by finite covers, with no compactness premise
on the target family. -/
theorem totallyBounded_range_of_controlled
    {ι A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (f : ι → A) (g : ι → B) {C : ℝ} (hC : 0 ≤ C)
    (hg : TotallyBounded (Set.range g))
    (hd : ∀ i j, dist (f i) (f j) ≤ C * dist (g i) (g j)) :
    TotallyBounded (Set.range f) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨t, ht, htf, hcover⟩ := Metric.finite_approx_of_totallyBounded hg δ hδ
  have he (b : t) : ∃ i, g i = b.val := ht b.property
  choose rep hrep using he
  letI := htf.to_subtype
  refine ⟨Set.range (fun b : t => f (rep b)), Set.finite_range _, ?_⟩
  rintro x ⟨i, rfl⟩
  obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_range_self i))
  apply Set.mem_iUnion₂.mpr
  refine ⟨f (rep ⟨b, hbt⟩), Set.mem_range_self _, ?_⟩
  change dist (f i) (f (rep ⟨b, hbt⟩)) < ε
  have hdist := hd i (rep ⟨b, hbt⟩)
  rw [hrep] at hdist
  have hsmall : C * δ < ε := by
    have heq : (C + 1) * δ = ε := by
      dsimp [δ]
      field_simp
    nlinarith
  exact hdist.trans_lt ((mul_le_mul_of_nonneg_left
    (show dist (g i) b ≤ δ from hb.le) hC).trans_lt hsmall)

/-- Every fixed smooth convolution has precompact L2 image on a bounded family
with a common compact support. -/
theorem fixed_mollifier_precompact (φ : ContDiffBump (0 : Space)) (R M : ℝ)
    (hM : 0 ≤ M) :
    TotallyBounded (Set.range (fun u :
      {u : L2Scalar // ‖u‖ ≤ M ∧ SupportedIn u (Metric.closedBall 0 R)} =>
        mollifyL2 φ u.val)) := by
  apply totallyBounded_range_of_controlled _
    (fun u : {u : L2Scalar // ‖u‖ ≤ M ∧ SupportedIn u (Metric.closedBall 0 R)} =>
      mollifiedRestriction φ u.val (R + φ.rOut))
    (C := ‖ballIndicator (R + φ.rOut)‖) (norm_nonneg _)
  · apply (mollified_restrictions_precompact φ (R + φ.rOut) M hM).totallyBounded.subset
    rintro f ⟨u, rfl⟩
    exact subset_closure (Set.mem_range.mpr ⟨⟨u.val, u.property.1⟩, rfl⟩)
  · intro u v
    exact mollified_L2_distance φ u.property.2 v.property.2

theorem totallyBounded_of_uniform_approximation
    {A : Type*} [PseudoMetricSpace A] (s : Set A) (f : ℕ → A → A)
    (hf : ∀ n, TotallyBounded (f n '' s))
    (ha : ∀ ε > 0, ∃ n, ∀ u ∈ s, dist u (f n u) < ε) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := ha (ε / 2) (half_pos hε)
  obtain ⟨t, htf, hcover⟩ :=
    Metric.totallyBounded_iff.mp (hf n) (ε / 2) (half_pos hε)
  refine ⟨t, htf, ?_⟩
  intro u hu
  obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_image_of_mem _ hu))
  refine Set.mem_iUnion₂.mpr ⟨b, hbt, ?_⟩
  exact (dist_triangle u (f n u) b).trans_lt
    (by simpa only [add_halves] using add_lt_add (hn u hu) hb)

/-- An actual weak Sobolev ball: distributional first derivatives in L2 and
essential support in a fixed closed ball. -/
def weakH1Ball (R M K : ℝ) : Set L2Scalar :=
  {u | ‖u‖ ≤ M ∧ SupportedIn u (Metric.closedBall 0 R) ∧
    ∃ D : Fin 3 → L2Scalar, (∀ i, HasWeakPartial u (D i) i) ∧ ∑ i, ‖D i‖ ≤ K}

/-- Concrete Rellich compactness in L2, proved from the actual weak partials,
explicit mollifiers, and finite-cover Arzelà–Ascoli. -/
theorem weakH1Ball_totallyBounded (R M K : ℝ) (hM : 0 ≤ M) :
    TotallyBounded (weakH1Ball R M K) := by
  apply totallyBounded_of_uniform_approximation _ (fun n => mollifyL2 (shrinkingBump n))
  · intro n
    apply (fixed_mollifier_precompact (shrinkingBump n) R M hM).subset
    rintro v ⟨u, hu, rfl⟩
    exact Set.mem_range.mpr ⟨⟨u, hu.1, hu.2.1⟩, rfl⟩
  · intro ε hε
    have ht : Tendsto (fun n => (shrinkingBump n).rOut * K) atTop (𝓝 0) := by
      simpa only [zero_mul] using shrinkingBump_tendsto.mul_const K
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
    refine ⟨n, ?_⟩
    intro u hu
    obtain ⟨D, hD, hDK⟩ := hu.2.2
    rw [dist_comm, dist_eq_norm]
    apply (weak_mollification_bound (shrinkingBump n)
      (supported_compact (isCompact_closedBall _ _) hu.2.1) hD).trans_lt
    exact (mul_le_mul_of_nonneg_left hDK (shrinkingBump n).rOut_pos.le).trans_lt hn

theorem weakH1Ball_compactClosure (R M K : ℝ) (hM : 0 ≤ M) :
    IsCompact (closure (weakH1Ball R M K)) :=
  isCompact_of_totallyBounded_isClosed
    (weakH1Ball_totallyBounded R M K hM).closure isClosed_closure

end OQ14.WeakCompactness

#print axioms OQ14.WeakCompactness.supported_compact
#print axioms OQ14.WeakCompactness.smoothScalar_global_difference
#print axioms OQ14.WeakCompactness.mollified_zero_outside
#print axioms OQ14.WeakCompactness.mollified_restrictions_precompact
#print axioms OQ14.WeakCompactness.mollified_L2_distance
#print axioms OQ14.WeakCompactness.totallyBounded_range_of_controlled
#print axioms OQ14.WeakCompactness.fixed_mollifier_precompact
#print axioms OQ14.WeakCompactness.totallyBounded_of_uniform_approximation
#print axioms OQ14.WeakCompactness.weakH1Ball_totallyBounded
#print axioms OQ14.WeakCompactness.weakH1Ball_compactClosure

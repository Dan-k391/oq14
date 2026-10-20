import L1Convolution
import WeakPoynting.Compactness
import Mathlib.Analysis.Normed.Operator.Compact

/-! # Compactly supported L2 kernels produce actual compact convolution families

The continuous representative is an actual L2 product integral. Its common
continuity modulus comes from the fixed kernel's L2 translation orbit.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.L2KernelCompact

open MeasureTheory Metric OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.WeakTranslations OQ14.WeakCompactness Filter
open scoped Topology

def row (q : L2Scalar) (x : Space) : L2Scalar :=
  Lp.compMeasurePreserving (fun y : Space => x-y) (Measure.measurePreserving_sub_left volume x) q

theorem row_ae (q : L2Scalar) (x : Space) :
    (row q x : Space → ℂ) =ᵐ[volume] fun y => q (x-y) :=
  Lp.coeFn_compMeasurePreserving q (Measure.measurePreserving_sub_left volume x)

theorem row_norm (q : L2Scalar) (x : Space) : ‖row q x‖ = ‖q‖ :=
  Lp.norm_compMeasurePreserving q (Measure.measurePreserving_sub_left volume x)

theorem row_continuous (q : L2Scalar) : Continuous (row q) := by
  let g : Space → C(Space, Space) := fun x => ⟨fun y => x-y, continuous_const.sub continuous_id⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.sub continuous_snd)
  exact continuous_const.compMeasurePreservingLp hg
    (fun x => Measure.measurePreserving_sub_left volume x) (by norm_num)

def value (q u : L2Scalar) (x : Space) : ℂ := scalarProduct u (row q x)

theorem value_integral (q u : L2Scalar) (x : Space) :
    value q u x = ∫ y, u y * q (x-y) := by
  rw [value, scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [row_ae q x] with y hy
  rw [hy]

theorem value_integrable (q u : L2Scalar) (x : Space) :
    Integrable (fun y => u y * q (x-y)) volume := by
  apply (scalarProduct_integrable u (row q x)).congr
  filter_upwards [row_ae q x] with y hy
  rw [hy]

theorem value_continuous (q u : L2Scalar) : Continuous (value q u) :=
  (scalarProduct u).continuous.comp (row_continuous q)

theorem value_norm_le (q u : L2Scalar) (x : Space) :
    ‖value q u x‖ ≤ ‖u‖ * ‖q‖ := by
  simpa only [value, row_norm] using scalarProduct_norm_le u (row q x)

theorem value_difference_le (q u : L2Scalar) (x y : Space) :
    dist (value q u x) (value q u y) ≤ ‖u‖ * dist (row q x) (row q y) := by
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [value, map_sub] using scalarProduct_norm_le u (row q x - row q y)

theorem value_zero_outside (q u : L2Scalar) (T S : ℝ)
    (hq : SupportedIn q (closedBall 0 T)) (hu : SupportedIn u (closedBall 0 S))
    (x : Space) (hx : T+S < ‖x‖) : value q u x = 0 := by
  rw [value_integral]
  apply integral_eq_zero_of_ae
  have hqx := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hq
  filter_upwards [hu, hqx] with y hy hqxy
  by_cases hs : y ∈ closedBall (0 : Space) S
  · have hn : x-y ∉ closedBall (0 : Space) T := by
      intro ht
      have hy' : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hs
      have ht' : ‖x-y‖ ≤ T := by simpa only [mem_closedBall, dist_zero_right] using ht
      have hh := norm_add_le (x-y) y
      rw [sub_add_cancel] at hh
      linarith
    simp only [hqxy hn, mul_zero, Pi.zero_apply]
  · simp only [hy hs, zero_mul, Pi.zero_apply]

def restriction (q u : L2Scalar) (S : ℝ) :
    BoundedContinuousFunction (closedBall (0 : Space) S) ℂ := by
  letI : CompactSpace (closedBall (0 : Space) S) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => value q u x, (value_continuous q u).comp continuous_subtype_val⟩

theorem restrictions_precompact (q : L2Scalar) (S M : ℝ) :
    IsCompact (closure (Set.range (fun u : {u : L2Scalar // ‖u‖ ≤ M} =>
      restriction q u.val S))) := by
  letI : CompactSpace (closedBall (0 : Space) S) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let A := Set.range (fun u : {u : L2Scalar // ‖u‖ ≤ M} => restriction q u.val S)
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (M * ‖q‖))
    (isCompact_closedBall _ _) A
  · intro f x hf
    obtain ⟨u, rfl⟩ := hf
    change ‖value q u.val x.val - 0‖ ≤ _
    rw [sub_zero]
    exact (value_norm_le q u.val x.val).trans
      (mul_le_mul_of_nonneg_right u.property (norm_nonneg _))
  · intro x
    let b : closedBall (0 : Space) S → ℝ := fun y => M * dist (row q x.val) (row q y.val)
    have hb : Tendsto b (nhds x) (nhds 0) := by
      have h : Continuous b := continuous_const.mul (continuous_const.dist
        ((row_continuous q).comp continuous_subtype_val))
      simpa only [b, dist_self, mul_zero] using h.continuousAt.tendsto (x := x)
    apply Metric.equicontinuousAt_of_continuity_modulus b hb
    filter_upwards with y f
    obtain ⟨u, hu⟩ := f.property
    rw [← hu]
    exact (value_difference_le q u.val x.val y.val).trans
      (mul_le_mul_of_nonneg_right u.property (dist_nonneg))

theorem operator_ae_value (q u : L2Scalar)
    (hq : Integrable (q : Space → ℂ) volume) (hu : Integrable (u : Space → ℂ) volume) :
    L1Convolution.operator q hq u =ᵐ[volume] value q u := by
  filter_upwards [L1Convolution.operator_ae_convolution q hq u hu] with x hx
  rw [hx, value_integral]
  change MeasureTheory.convolution q u (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards with y
  exact mul_comm _ _

theorem operator_L2_distance (q : L2Scalar)
    (hqI : Integrable (q : Space → ℂ) volume) (T S : ℝ)
    (hq : SupportedIn q (closedBall 0 T)) (u v : L2Scalar)
    (hu : SupportedIn u (closedBall 0 S)) (hv : SupportedIn v (closedBall 0 S)) :
    dist (L1Convolution.operator q hqI u) (L1Convolution.operator q hqI v) ≤
      ‖ballIndicator (T+S)‖ * dist (restriction q u (T+S)) (restriction q v (T+S)) := by
  have huI := NewtonL1L2.compact_supported_integrable u _ (isCompact_closedBall _ _) hu
  have hvI := NewtonL1L2.compact_supported_integrable v _ (isCompact_closedBall _ _) hv
  rw [dist_eq_norm, mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (L1Convolution.operator q hqI u) (L1Convolution.operator q hqI v),
    operator_ae_value q u hqI huI, operator_ae_value q v hqI hvI,
    indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := measurableSet_closedBall)
      (hμs := (isCompact_closedBall (0 : Space) (T+S)).measure_lt_top.ne) (c := (1 : ℂ))]
    with x hx hxu hxv hxi
  rw [hx]
  simp only [Pi.sub_apply, hxu, hxv]
  by_cases hs : x ∈ closedBall (0 : Space) (T+S)
  · have hi : ballIndicator (T+S) x = 1 := hxi.trans (Set.indicator_of_mem hs _)
    rw [hi, norm_one, mul_one]
    exact BoundedContinuousFunction.dist_coe_le_dist
      (f := restriction q u (T+S)) (g := restriction q v (T+S))
      (⟨x,hs⟩ : closedBall (0 : Space) (T+S))
  · have hn : T+S < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hs
    rw [value_zero_outside q u T S hq hu x hn, value_zero_outside q v T S hq hv x hn]
    simp only [sub_self, norm_zero]
    positivity

/-- Precompactness of the actual previously constructed L1 convolution
operator on a bounded family with a common compact source support. -/
theorem operator_precompact (q : L2Scalar) (hqI : Integrable (q : Space → ℂ) volume)
    (T S M : ℝ) (hq : SupportedIn q (closedBall 0 T)) :
    TotallyBounded (Set.range (fun u :
      {u : L2Scalar // ‖u‖ ≤ M ∧ SupportedIn u (closedBall 0 S)} =>
        L1Convolution.operator q hqI u.val)) := by
  apply totallyBounded_range_of_controlled _
    (fun u : {u : L2Scalar // ‖u‖ ≤ M ∧ SupportedIn u (closedBall 0 S)} =>
      restriction q u.val (T+S)) (C := ‖ballIndicator (T+S)‖) (norm_nonneg _)
  · apply (restrictions_precompact q (T+S) M).totallyBounded.subset
    rintro f ⟨u, rfl⟩
    exact subset_closure (Set.mem_range.mpr ⟨⟨u.val,u.property.1⟩,rfl⟩)
  · intro u v
    exact operator_L2_distance q hqI T S hq u.val v.val u.property.2 v.property.2

theorem operator_comp_isCompact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (q : L2Scalar) (hqI : Integrable (q : Space → ℂ) volume) (T S : ℝ)
    (hq : SupportedIn q (closedBall 0 T)) (B : V →L[ℂ] L2Scalar)
    (hB : ∀ u, SupportedIn (B u) (closedBall 0 S)) :
    IsCompactOperator ((L1Convolution.operator q hqI).comp B) := by
  let A := Set.range (fun u :
    {u : L2Scalar // ‖u‖ ≤ ‖B‖ ∧ SupportedIn u (closedBall 0 S)} =>
      L1Convolution.operator q hqI u.val)
  have hA : IsCompact (closure A) :=
    isCompact_of_totallyBounded_isClosed (operator_precompact q hqI T S ‖B‖ hq).closure isClosed_closure
  apply (isCompactOperator_iff_image_closedBall_subset_compact (f :=
    ((L1Convolution.operator q hqI).comp B).toLinearMap) (r := 1) (by norm_num)).mpr
  refine ⟨closure A, hA, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  apply subset_closure
  have hn : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hb : ‖B u‖ ≤ ‖B‖ := (B.le_opNorm u).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _))
  exact Set.mem_range.mpr ⟨⟨B u,hb,hB u⟩,rfl⟩

end OQ14.L2KernelCompact

#print axioms OQ14.L2KernelCompact.row_ae
#print axioms OQ14.L2KernelCompact.row_norm
#print axioms OQ14.L2KernelCompact.row_continuous
#print axioms OQ14.L2KernelCompact.value_integral
#print axioms OQ14.L2KernelCompact.value_integrable
#print axioms OQ14.L2KernelCompact.value_continuous
#print axioms OQ14.L2KernelCompact.value_norm_le
#print axioms OQ14.L2KernelCompact.value_difference_le
#print axioms OQ14.L2KernelCompact.value_zero_outside
#print axioms OQ14.L2KernelCompact.restrictions_precompact
#print axioms OQ14.L2KernelCompact.operator_ae_value
#print axioms OQ14.L2KernelCompact.operator_L2_distance
#print axioms OQ14.L2KernelCompact.operator_precompact
#print axioms OQ14.L2KernelCompact.operator_comp_isCompact

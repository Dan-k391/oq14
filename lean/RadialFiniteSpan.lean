import PolarMomentOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compact radial restriction and closed two-mode spans in the actual radial L2 space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.RadialFiniteSpan
open MeasureTheory Set Filter OQ14.PolarMomentOperator
open scoped Topology

def cut (s : Set ℝ) (hs : MeasurableSet s) (f : RadialL2) : RadialL2 :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)

theorem cut_actual (s : Set ℝ) (hs : MeasurableSet s) (f : RadialL2) :
    (cut s hs f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] s.indicator f :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

theorem cut_add (s : Set ℝ) (hs : MeasurableSet s) (f g : RadialL2) :
    cut s hs (f+g) = cut s hs f + cut s hs g := by
  apply Lp.ext
  filter_upwards [cut_actual s hs (f+g), cut_actual s hs f, cut_actual s hs g,
    Lp.coeFn_add f g, Lp.coeFn_add (cut s hs f) (cut s hs g)] with r hfg hf hg ha hb
  rw [hfg, hb, Pi.add_apply, hf, hg]
  by_cases hr : r ∈ s
  · rw [indicator_of_mem hr, indicator_of_mem hr, indicator_of_mem hr, ha]
    rfl
  · simp only [indicator_of_not_mem hr, add_zero]

theorem cut_smul (s : Set ℝ) (hs : MeasurableSet s) (a : ℂ) (f : RadialL2) :
    cut s hs (a • f) = a • cut s hs f := by
  apply Lp.ext
  filter_upwards [cut_actual s hs (a • f), cut_actual s hs f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (cut s hs f)] with r haf hf ha hb
  rw [haf, hb, Pi.smul_apply, hf]
  by_cases hr : r ∈ s <;> simp [hr, ha]

def cutLinear (s : Set ℝ) (hs : MeasurableSet s) : RadialL2 →ₗ[ℂ] RadialL2 where
  toFun := cut s hs
  map_add' := cut_add s hs
  map_smul' := cut_smul s hs

def cutOperator (s : Set ℝ) (hs : MeasurableSet s) : RadialL2 →L[ℂ] RadialL2 :=
  (cutLinear s hs).mkContinuous 1 (fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [cut_actual s hs f] with r hr
    change ‖cut s hs f r‖ ≤ 1 * ‖f r‖
    rw [hr, one_mul]
    by_cases hs : r ∈ s
    · simp only [indicator_of_mem hs, le_refl]
    · simp only [indicator_of_not_mem hs, norm_zero, norm_nonneg])

theorem compact_memLp (a b : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) :
    MemLp ((Icc a b).indicator f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hm : MemLp f 2 (volume.restrict (Icc a b)) :=
    MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hC r hr)
  have hi : MemLp ((Icc a b).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr hm
  exact hi.mono_measure Measure.restrict_le_self

def compactMode (a b : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) : RadialL2 :=
  (compact_memLp a b f hf).toLp ((Icc a b).indicator f)

theorem compactMode_actual (a b : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) :
    (compactMode a b f hf : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] (Icc a b).indicator f :=
  (compact_memLp a b f hf).coeFn_toLp

theorem limit_in_two_mode_span (v w : RadialL2) (f : ℕ → RadialL2) (g : RadialL2)
    (hlim : Tendsto f atTop (𝓝 g))
    (hf : ∀ᶠ n : ℕ in atTop, f n ∈ Submodule.span ℂ ({v,w} : Set RadialL2)) :
    g ∈ Submodule.span ℂ ({v,w} : Set RadialL2) := by
  let S := Submodule.span ℂ ({v,w} : Set RadialL2)
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  exact S.closed_of_finiteDimensional.mem_of_tendsto hlim hf

end OQ14.RadialFiniteSpan
#print axioms OQ14.RadialFiniteSpan.cutOperator
#print axioms OQ14.RadialFiniteSpan.compact_memLp
#print axioms OQ14.RadialFiniteSpan.compactMode_actual
#print axioms OQ14.RadialFiniteSpan.limit_in_two_mode_span

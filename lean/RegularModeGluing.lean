import WeakRegularBallBasis
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Consistent regular radial amplitudes on the entire punctured ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RegularModeGluing
open Complex MeasureTheory Set Filter OQ14.RadialOriginSelection
open scoped Topology

theorem regular_nonzero_somewhere (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ r ∈ Ioo a b, regular l k r ≠ 0 := by
  by_contra hn
  push_neg at hn
  let r := (a+b)/2
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
  have he : regular l k =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact hn t ht
  have hd : regularD l k r = 0 := (regular_hasDerivAt l k r).unique
    ((hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq he)
  have hW := regular_outgoing_wronskian l k hk r (ne_of_gt (lt_trans ha hr.1))
  rw [hn r hr, hd, zero_mul, mul_zero, sub_zero] at hW
  exact mul_ne_zero I_ne_zero hk hW.symm

theorem coefficient_unique (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (c d : ℂ)
    (he : (fun r => c * regular l k r) =ᵐ[volume.restrict (Icc a b)]
      (fun r => d * regular l k r)) : c = d := by
  have hc : Continuous (regular l k) := continuous_iff_continuousAt.mpr
    (fun r => (regular_hasDerivAt l k r).continuousAt)
  have heo := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self he
  have hpoint := Measure.eqOn_open_of_ae_eq heo isOpen_Ioo
    (continuous_const.mul hc).continuousOn (continuous_const.mul hc).continuousOn
  obtain ⟨r,hr,hn⟩ := regular_nonzero_somewhere l k hk a b ha hab
  exact mul_right_cancel₀ hn (hpoint hr)

theorem glue (L : ℝ) (hL : 0 < L) (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (f : ℝ → ℂ)
    (hloc : ∀ a b : ℝ, 0 < a → b < L → ∃ c : ℂ,
      f =ᵐ[volume.restrict (Icc a b)] fun r => c * regular l k r) :
    ∃ c : ℂ, f =ᵐ[volume.restrict (Ioo 0 L)] fun r => c * regular l k r := by
  obtain ⟨c,hc⟩ := hloc (L/3) (2*L/3) (by linarith) (by linarith)
  have hfixed (a b : ℝ) (ha : 0 < a) (hb : b < L) :
      f =ᵐ[volume.restrict (Icc a b)] fun r => c * regular l k r := by
    obtain ⟨d,hd⟩ := hloc (min a (L/3)) (max b (2*L/3))
      (lt_min ha (by linarith)) (max_lt hb (by linarith))
    have hanchor : Icc (L/3) (2*L/3) ⊆ Icc (min a (L/3)) (max b (2*L/3)) :=
      fun r hr => ⟨(min_le_right a (L/3)).trans hr.1, hr.2.trans (le_max_right b (2*L/3))⟩
    have heq := hc.symm.trans (ae_restrict_of_ae_restrict_of_subset hanchor hd)
    have hcd : c = d := coefficient_unique l k hk (L/3) (2*L/3)
      (by linarith) (by linarith) c d heq
    rw [← hcd] at hd
    have hsub : Icc a b ⊆ Icc (min a (L/3)) (max b (2*L/3)) :=
      fun r hr => ⟨(min_le_left a (L/3)).trans hr.1, hr.2.trans (le_max_left b (2*L/3))⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hd
  have hq (a b : ℚ) : ∀ᵐ r : ℝ, 0 < (a : ℝ) → (b : ℝ) < L →
      r ∈ Icc (a : ℝ) (b : ℝ) → f r = c * regular l k r := by
    by_cases ha : 0 < (a : ℝ)
    · by_cases hb : (b : ℝ) < L
      · have h := (ae_restrict_iff' measurableSet_Icc).mp (hfixed a b ha hb)
        filter_upwards [h] with r hr _ _ hmem
        exact hr hmem
      · filter_upwards with r _ hbr
        exact (hb hbr).elim
    · filter_upwards with r har
      exact (ha har).elim
  have hall : ∀ᵐ r : ℝ, ∀ a b : ℚ, 0 < (a : ℝ) → (b : ℝ) < L →
      r ∈ Icc (a : ℝ) (b : ℝ) → f r = c * regular l k r :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (hq a))
  refine ⟨c, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  filter_upwards [hall] with r hr hrL
  obtain ⟨a,ha,har⟩ := exists_rat_btwn hrL.1
  obtain ⟨b,hrb,hb⟩ := exists_rat_btwn hrL.2
  exact hr a b ha hb ⟨har.le,hrb.le⟩

end OQ14.RegularModeGluing
#print axioms OQ14.RegularModeGluing.regular_nonzero_somewhere
#print axioms OQ14.RegularModeGluing.coefficient_unique
#print axioms OQ14.RegularModeGluing.glue

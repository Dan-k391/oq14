import AnalyticOutgoingSelection
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.OutgoingModeGluing
open Complex MeasureTheory Set Filter OQ14.RadialRellich
open scoped Topology

theorem outgoing_nonzero_somewhere (l : ℕ) (z : ℂ) (hz : z ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ r ∈ Ioo a b, outgoing l z r ≠ 0 := by
  by_contra hn
  push_neg at hn
  let r := (a+b)/2
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
  have he : outgoing l z =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact hn t ht
  have hd : outgoingD l z r = 0 := (outgoing_hasDerivAt l z hz r (ne_of_gt (lt_trans ha hr.1))).unique
    ((hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq he)
  have hw := radial_wronskian l z hz r (ne_of_gt (lt_trans ha hr.1))
  rw [hn r hr, hd, zero_mul, mul_zero, sub_zero] at hw
  exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz hw.symm

theorem coefficient_unique (l : ℕ) (z : ℂ) (hz : z ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (c d : ℂ)
    (he : (fun r => c * outgoing l z r) =ᵐ[volume.restrict (Icc a b)]
      (fun r => d * outgoing l z r)) : c = d := by
  have hc : ContinuousOn (outgoing l z) (Ioo a b) := fun r hr =>
    (outgoing_hasDerivAt l z hz r (ne_of_gt (lt_trans ha hr.1))).continuousAt.continuousWithinAt
  have heo := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self he
  have hpoint := Measure.eqOn_open_of_ae_eq heo isOpen_Ioo
    (continuousOn_const.mul hc) (continuousOn_const.mul hc)
  obtain ⟨r,hr,hn⟩ := outgoing_nonzero_somewhere l z hz a b ha hab
  exact mul_right_cancel₀ hn (hpoint hr)

theorem glue (L : ℝ) (hL : 1 < L) (l : ℕ) (z : ℂ) (hz : z ≠ 0)
    (f : ℝ → ℂ)
    (hloc : ∀ a b : ℝ, 1 < a → a < b → b < L → ∃ c : ℂ,
      f =ᵐ[volume.restrict (Icc a b)] fun r => c * outgoing l z r) :
    ∃ c : ℂ, f =ᵐ[volume.restrict (Ioo 1 L)] fun r => c * outgoing l z r := by
  let a0 := (2+L)/3
  let b0 := (1+2*L)/3
  have ha0 : 1 < a0 := by dsimp [a0]; linarith
  have hab0 : a0 < b0 := by dsimp [a0,b0]; linarith
  have hb0 : b0 < L := by dsimp [b0]; linarith
  obtain ⟨c,hc⟩ := hloc a0 b0 ha0 hab0 hb0
  have hfixed (a b : ℝ) (ha : 1 < a) (hab : a < b) (hb : b < L) :
      f =ᵐ[volume.restrict (Icc a b)] fun r => c * outgoing l z r := by
    obtain ⟨d,hd⟩ := hloc (min a a0) (max b b0)
      (lt_min ha ha0) (by linarith [min_le_right a a0, le_max_right b b0]) (max_lt hb hb0)
    have hanchor : Icc a0 b0 ⊆ Icc (min a a0) (max b b0) :=
      fun r hr => ⟨(min_le_right a a0).trans hr.1, hr.2.trans (le_max_right b b0)⟩
    have heq := hc.symm.trans (ae_restrict_of_ae_restrict_of_subset hanchor hd)
    have hcd : c = d := coefficient_unique l z hz a0 b0 (by linarith) hab0 c d heq
    rw [← hcd] at hd
    have hsub : Icc a b ⊆ Icc (min a a0) (max b b0) :=
      fun r hr => ⟨(min_le_left a a0).trans hr.1, hr.2.trans (le_max_left b b0)⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hd
  have hq (a b : ℚ) : ∀ᵐ r : ℝ, 1 < (a : ℝ) → (a : ℝ) < (b : ℝ) → (b : ℝ) < L →
      r ∈ Icc (a : ℝ) (b : ℝ) → f r = c * outgoing l z r := by
    by_cases ha : 1 < (a : ℝ)
    · by_cases hab : (a : ℝ) < (b : ℝ)
      · by_cases hb : (b : ℝ) < L
        · have h := (ae_restrict_iff' measurableSet_Icc).mp (hfixed a b ha hab hb)
          filter_upwards [h] with r hr _ _ _ hmem
          exact hr hmem
        · filter_upwards with r _ _ hbr
          exact (hb hbr).elim
      · filter_upwards with r _ habr
        exact (hab habr).elim
    · filter_upwards with r har
      exact (ha har).elim
  have hall : ∀ᵐ r : ℝ, ∀ a b : ℚ, 1 < (a : ℝ) → (a : ℝ) < (b : ℝ) → (b : ℝ) < L →
      r ∈ Icc (a : ℝ) (b : ℝ) → f r = c * outgoing l z r :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (hq a))
  refine ⟨c, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  filter_upwards [hall] with r hr hrL
  obtain ⟨a,ha,har⟩ := exists_rat_btwn hrL.1
  obtain ⟨b,hrb,hb⟩ := exists_rat_btwn hrL.2
  exact hr a b ha (lt_trans har hrb) hb ⟨har.le,hrb.le⟩

theorem actual_exterior_moment (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (u : VectorFourier.VectorL2) (i : Fin 3)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 1 T),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)
        (SphericalMomentEquation.angularPolynomial p) r = c * outgoing l z r := by
  apply glue T hT l z hz _
  intro a b ha hab hb
  exact AnalyticOutgoingSelection.outgoing_moment n hn T a b ha hab hb.le u p l hp hh i z hz

#print axioms OQ14.OutgoingModeGluing.actual_exterior_moment
#print axioms OQ14.OutgoingModeGluing.outgoing_nonzero_somewhere
#print axioms OQ14.OutgoingModeGluing.coefficient_unique
#print axioms OQ14.OutgoingModeGluing.glue
end OQ14.OutgoingModeGluing


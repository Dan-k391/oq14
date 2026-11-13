import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02LogSquare
open MeasureTheory Set Filter
open scoped Topology

 theorem positive_bound : ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Ioo (0 : ℝ) d,
    ‖(Real.log x)^2‖ ≤ ‖x ^ (-(1/2 : ℝ))‖ := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := -(1/2 : ℝ)) 2 (by norm_num)).bound (by norm_num : (0 : ℝ) < 1)
  have h' : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖(Real.log x)^2‖ ≤ ‖x ^ (-(1/2 : ℝ))‖ := by
    filter_upwards [h] with x hx
    simpa [Real.rpow_two, abs_sq] using hx
  obtain ⟨d, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h'
  exact ⟨d, hd, hsub⟩


theorem interval_log_sq (a b : ℝ) : IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume a b := by
  obtain ⟨d, hd, hb⟩ := positive_bound
  have hsmall : IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume 0 d := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hd.le, integrableOn_Icc_iff_integrableOn_Ioo]
    have hi : IntegrableOn (fun x : ℝ => x ^ (-(1/2 : ℝ))) (Ioo 0 d) := by
      apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hd.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := d) (by norm_num))).mono_set
      exact Ioo_subset_Icc_self
    apply hi.mono' ((Real.measurable_log.pow_const 2).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)] using hb x hx
  have hpos : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume 0 c := by
    intro c hc
    by_cases hcd : c ≤ d
    · apply hsmall.mono_set
      simpa only [uIcc_of_le hc, uIcc_of_le hd.le] using Icc_subset_Icc_right hcd
    · have hdc : d ≤ c := le_of_not_ge hcd
      have hcont : ContinuousOn (fun x : ℝ => (Real.log x)^2) (Icc d c) := by
        apply (continuousOn_id.log ?_).pow
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le hd hx.1)
      exact hsmall.trans (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hdc]; exact hcont.integrableOn_compact isCompact_Icc)
  have hall : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume 0 c := by
    intro c
    by_cases hc : 0 ≤ c
    · exact hpos c hc
    · have h := (IntervalIntegrable.iff_comp_neg).mp (hpos (-c) (by linarith))
      simpa [Real.log_neg_eq_log] using h
  exact (hall a).symm.trans (hall b)

theorem translated_log_sq_integrable (r a b : ℝ) :
    IntegrableOn (fun s : ℝ => (Real.log |r-s|)^2) (Icc a b) := by
  by_cases hab : a ≤ b
  · have h := (interval_log_sq (r-a) (r-b)).comp_sub_left r
    have h' : IntervalIntegrable (fun s : ℝ => (Real.log |r-s|)^2) volume a b := by
      simpa [Real.log_abs] using h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp h'
  · simp [Icc_eq_empty hab]

theorem locallyIntegrable_log_sq : LocallyIntegrable (fun x : ℝ => (Real.log x)^2) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le (by have := abs_nonneg R; linarith : -|R| ≤ |R|)).mp
    (interval_log_sq (-|R|) |R|)
  apply h.mono_set
  intro x hx
  have hx' := hR hx
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx'
  exact ⟨by linarith [neg_abs_le x, le_abs_self x, le_abs_self R], by linarith [le_abs_self x, le_abs_self R]⟩

#print axioms OQ14.Packet02LogSquare.locallyIntegrable_log_sq
#print axioms OQ14.Packet02LogSquare.positive_bound
#print axioms OQ14.Packet02LogSquare.interval_log_sq
#print axioms OQ14.Packet02LogSquare.translated_log_sq_integrable
end OQ14.Packet02LogSquare

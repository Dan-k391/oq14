import KernelIntegrability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Packet02LogSquare

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02RadialLog
open MeasureTheory Set OQ14.Maxwell

def ratioLog (r s : ℝ) : ℝ := Real.log ((r+s)/|r-s|)

theorem ratioLog_tail_bound (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 2*r < s) :
    |ratioLog r s| ≤ 4*r/s := by
  have hs0 : 0 < s := by linarith
  have hd : 0 < s-r := by linarith
  have hq : 0 < (r+s)/(s-r) := div_pos (by linarith) hd
  have hq1 : 1 ≤ (r+s)/(s-r) := (le_div_iff₀ hd).mpr (by linarith)
  rw [ratioLog, abs_of_neg (by linarith : r-s < 0)]
  simp only [neg_sub]
  rw [abs_of_nonneg (Real.log_nonneg hq1)]
  apply (Real.log_le_sub_one_of_pos hq).trans
  calc
    _ = 2*r/(s-r) := by field_simp; ring
    _ ≤ 4*r/s := (div_le_div_iff₀ hd hs0).mpr (by nlinarith)

theorem ratioLog_sq_tail (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (ratioLog r s)^2) (Ioi (2*r)) := by
  have hp : IntegrableOn (fun s : ℝ => (s⁻¹)^2) (Ioi (2*r)) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
      (show 0 < 2*r by positivity)).congr_fun _ measurableSet_Ioi
    intro s hs
    change 2*r < s at hs
    change s ^ (-2 : ℝ) = (s⁻¹)^2
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (show 0 ≤ s by linarith), Real.rpow_two, inv_pow]
  have hm : Measurable (fun s : ℝ => (ratioLog r s)^2) := by
    unfold ratioLog
    fun_prop
  apply (hp.const_mul ((4*r)^2)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 2*r < s at hs
  have hb := ratioLog_tail_bound r hr s hs
  have hpos : 0 ≤ 4*r/s := le_of_lt (div_pos (by positivity) (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : (ratioLog r s)^2 ≤ (4*r/s)^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hpos] using hb)
  simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hsq

theorem ratioLog_sq_local (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (ratioLog r s)^2) (Ioc 0 (2*r)) := by
  have hfirst : IntegrableOn (fun s : ℝ => (Real.log (r+s))^2) (Icc 0 (2*r)) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.pow
    exact (continuous_const.add continuous_id).continuousOn.log
      (fun s hs => ne_of_gt (by change 0 < r+s; linarith [hs.1]))
  have hsecond := Packet02LogSquare.translated_log_sq_integrable r 0 (2*r)
  have hsum : IntegrableOn (fun s : ℝ => 2 * (Real.log (r+s))^2 +
      2 * (Real.log |r-s|)^2) (Icc 0 (2*r)) :=
    (hfirst.const_mul 2).add (hsecond.const_mul 2)
  have hm : Measurable (fun s : ℝ => (ratioLog r s)^2) := by unfold ratioLog; fun_prop
  apply (hsum.mono_set Ioc_subset_Icc_self).mono' hm.aestronglyMeasurable
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using (measure_singleton r)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae hne] with s hs hsr
  have hden : |r-s| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hsr))
  have hnum : r+s ≠ 0 := ne_of_gt (by linarith [hs.1])
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ratioLog, Real.log_div hnum hden]
  nlinarith [sq_nonneg (Real.log (r+s) + Real.log |r-s|)]

theorem ratioLog_sq_integrable (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => (ratioLog r s)^2) (Ioi 0) := by
  have he : Ioc (0 : ℝ) (2*r) ∪ Ioi (2*r) = Ioi 0 := by
    ext s
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hs
      by_cases h : s ≤ 2*r
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← he, integrableOn_union]
  exact ⟨ratioLog_sq_local r hr, ratioLog_sq_tail r hr⟩

theorem profile_memLp (r : ℝ) (hr : 0 < r) :
    MemLp (fun y : Space => (2 * Real.pi / (r * ‖y‖)) *
      Real.log ((r+‖y‖)/|r-‖y‖|)) 2 volume := by
  have hm : Measurable (fun y : Space => (2 * Real.pi / (r * ‖y‖)) *
      Real.log ((r+‖y‖)/|r-‖y‖|)) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi : IntegrableOn (fun s : ℝ => (2*Real.pi/r)^2 * (ratioLog r s)^2) (Ioi 0) :=
    (ratioLog_sq_integrable r hr).const_mul ((2*Real.pi/r)^2)
  have hrad : IntegrableOn (fun s : ℝ => s^2 * ((2*Real.pi/(r*s))*ratioLog r s)^2)
      (Ioi 0) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro s hs
    change 0 < s at hs
    change (2*Real.pi/r)^2 * (ratioLog r s)^2 = s^2 * ((2*Real.pi/(r*s))*ratioLog r s)^2
    field_simp [ne_of_gt hr, ne_of_gt hs]
    ring
  simpa only [Real.norm_eq_abs, sq_abs, ratioLog] using
    KernelIntegrability.radial_integrable (fun s => ((2*Real.pi/(r*s))*ratioLog r s)^2) hrad

end OQ14.Packet02RadialLog
#print axioms OQ14.Packet02RadialLog.ratioLog_tail_bound
#print axioms OQ14.Packet02RadialLog.ratioLog_sq_tail
#print axioms OQ14.Packet02RadialLog.ratioLog_sq_local
#print axioms OQ14.Packet02RadialLog.ratioLog_sq_integrable
#print axioms OQ14.Packet02RadialLog.profile_memLp

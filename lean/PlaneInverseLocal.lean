import PlaneInverseAnnulus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Actual local plane envelopes with uniform inverse-distance and logarithmic inverse-square masses. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.PlaneInverseLocal

open MeasureTheory Metric Set PlaneInverseCube PlaneInverseAnnulus
open scoped Topology

def envelope (p : ℕ) (d M : ℝ) (q : Plane) : ℝ :=
  (closedBall (0 : Plane) d).indicator (fun _ => d⁻¹^p) q+PlaneInverseAnnulus.profile p d M ‖q‖

theorem envelope_one_integrable (d M : ℝ) (hd : 0 < d) : Integrable (envelope 1 d M) :=
  ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top))).add
      (profile_one_integrable d M hd)

theorem envelope_two_integrable (d M : ℝ) (hd : 0 < d) : Integrable (envelope 2 d M) :=
  ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top))).add
      (profile_two_integrable d M hd)

theorem envelope_nonnegative (p : ℕ) (d M : ℝ) (hd : 0 ≤ d) (q : Plane) :
    0 ≤ envelope p d M q := by
  unfold envelope PlaneInverseAnnulus.profile
  exact add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) q)
    (Set.indicator_nonneg (fun t ht => by
      have ht0 : 0 < t := hd.trans_lt ht.1
      positivity) ‖q‖)

private theorem disk_volume (d : ℝ) (hd : 0 ≤ d) :
    volume.real (closedBall (0 : Plane) d)=d^2*Real.pi := by
  simp only [measureReal_def, EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd,
    ENNReal.toReal_ofReal Real.pi_pos.le]

theorem envelope_one_integral (d M : ℝ) (hd : 0 < d) (hdM : d ≤ M) :
    (∫ q : Plane, envelope 1 d M q)=Real.pi*d+diskConstant*(M-d) := by
  unfold envelope
  rw [integral_add ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top)))
    (profile_one_integrable d M hd), integral_indicator_const _ isClosed_closedBall.measurableSet,
    profile_one_integral d M hd hdM]
  change volume.real (closedBall (0 : Plane) d)*d⁻¹^1+_=_
  rw [disk_volume d hd.le]
  field_simp
  ring

theorem envelope_one_mass (d M : ℝ) (hd : 0 < d) (hdM : d ≤ M) :
    (∫ q : Plane, envelope 1 d M q) ≤ 2*Real.pi*M := by
  rw [envelope_one_integral d M hd hdM]
  have hc : diskConstant=2*Real.pi := by
    simp [diskConstant, measureReal_def, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hc]
  nlinarith [Real.pi_pos]

theorem envelope_two_integral (d M : ℝ) (hd : 0 < d) (hdM : d ≤ M) :
    (∫ q : Plane, envelope 2 d M q)=Real.pi+diskConstant*Real.log (M/d) := by
  unfold envelope
  rw [integral_add ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top)))
    (profile_two_integrable d M hd), integral_indicator_const _ isClosed_closedBall.measurableSet,
    profile_two_integral d M hd hdM]
  change volume.real (closedBall (0 : Plane) d)*d⁻¹^2+_=_
  rw [disk_volume d hd.le]
  field_simp

theorem inverse_pow_le_envelope (p : ℕ) (d M : ℝ) (hd : 0 < d)
    (q : Plane) (r : ℝ) (hdr : d ≤ r) (hqr : ‖q‖ ≤ r) (hqM : ‖q‖ ≤ M) :
    r⁻¹^p ≤ envelope p d M q := by
  by_cases hq : ‖q‖ ≤ d
  · have he : envelope p d M q=d⁻¹^p := by
      simp [envelope, PlaneInverseAnnulus.profile, Set.indicator, mem_closedBall,
        dist_zero_right, hq, not_lt.mpr hq]
    rw [he]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hd.trans_le hdr).le)
      (inv_le_inv₀ (hd.trans_le hdr) hd |>.mpr hdr) p
  · have hqd : d < ‖q‖ := lt_of_not_ge hq
    have he : envelope p d M q=‖q‖⁻¹^p := by
      simp [envelope, PlaneInverseAnnulus.profile, Set.indicator, mem_closedBall,
        dist_zero_right, hq, hqd, hqM]
    rw [he]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hd.trans_le hdr).le)
      (inv_le_inv₀ (hd.trans_le hdr) (hd.trans hqd) |>.mpr hqr) p

end OQ14.PlaneInverseLocal

#print axioms OQ14.PlaneInverseLocal.envelope_one_integrable
#print axioms OQ14.PlaneInverseLocal.envelope_two_integrable
#print axioms OQ14.PlaneInverseLocal.envelope_nonnegative
#print axioms OQ14.PlaneInverseLocal.envelope_one_integral
#print axioms OQ14.PlaneInverseLocal.envelope_one_mass
#print axioms OQ14.PlaneInverseLocal.envelope_two_integral
#print axioms OQ14.PlaneInverseLocal.inverse_pow_le_envelope

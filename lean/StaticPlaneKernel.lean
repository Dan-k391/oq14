import StaticBallDipole
import PlaneSourceKernel

/-! Actual inverse-cube plane envelopes for a positive source height. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.StaticPlaneKernel

open MeasureTheory Metric Set PlaneInverseCube
open scoped Topology

abbrev Space := FourierL2.Space

def envelope (d : ℝ) (q : Plane) : ℝ :=
  (closedBall (0 : Plane) d).indicator (fun _ => d⁻¹^3) q+profile d ‖q‖

theorem envelope_integrable (d : ℝ) (hd : 0 < d) : Integrable (envelope d) := by
  exact ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top))).add
      (inverse_cube_integrable d hd)

theorem envelope_nonnegative (d : ℝ) (hd : 0 ≤ d) (q : Plane) : 0 ≤ envelope d q := by
  unfold envelope profile
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ => by positivity) q
  · exact Set.indicator_nonneg (fun t ht => by
      simp only [mem_Ioi] at ht
      have ht0 : 0 < t := hd.trans_lt ht
      positivity) ‖q‖

theorem envelope_integral (d : ℝ) (hd : 0 < d) :
    (∫ q : Plane, envelope d q) = (Real.pi+diskConstant)/d := by
  have hv : volume.real (closedBall (0 : Plane) d) = d^2*Real.pi := by
    simp only [measureReal_def, EuclideanSpace.volume_closedBall_fin_two,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  unfold envelope
  rw [integral_add
    ((integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) d).measure_lt_top)))
    (inverse_cube_integrable d hd), integral_indicator_const _ isClosed_closedBall.measurableSet,
    inverse_cube_integral d hd]
  change volume.real (closedBall (0 : Plane) d)*d⁻¹^3+diskConstant/d = _
  rw [hv]
  field_simp
  ring

theorem inverse_cube_le_envelope (d : ℝ) (hd : 0 < d) (q : Plane) (r : ℝ)
    (hdr : d ≤ r) (hqr : ‖q‖ ≤ r) : r⁻¹^3 ≤ envelope d q := by
  by_cases hq : ‖q‖ ≤ d
  · have he : envelope d q = d⁻¹^3 := by
      simp [envelope, profile, Set.indicator, mem_closedBall, dist_zero_right, hq, not_lt.mpr hq]
    rw [he]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hd.trans_le hdr).le)
      (inv_le_inv₀ (hd.trans_le hdr) hd |>.mpr hdr) 3
  · have hqd : d < ‖q‖ := lt_of_not_ge hq
    have he : envelope d q = ‖q‖⁻¹^3 := by
      simp [envelope, profile, Set.indicator, mem_closedBall, dist_zero_right, hq, hqd, inv_pow]
    rw [he]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (hd.trans_le hdr).le)
      (inv_le_inv₀ (hd.trans_le hdr) (hd.trans hqd) |>.mpr hqr) 3

theorem static_hessian_bound (z : Space) (hz : z ≠ 0) (i j : Fin 3) :
    ‖GreenKernel.phiHessian 0 z i j‖ ≤ (1/Real.pi)*‖z‖⁻¹^3 := by
  let V := volume.real (ball (0 : Space) 1)
  have hv : V = Real.pi*4/3 := by
    simp only [V, measureReal_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal zero_le_one,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3), one_pow, one_mul]
  have hp : 0 < V := by rw [hv]; positivity
  apply (mul_le_mul_left hp).mp
  calc
    V*‖GreenKernel.phiHessian 0 z i j‖ = ‖StaticBallHessian.exterior 1 ‖z‖ i j z‖ := by
      rw [StaticBallDipole.exterior_eq_volume_kernel (0 : Space) 1 zero_le_one z hz,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
    _ ≤ (4/3 : ℝ)*(1/‖z‖^3) := by
      simpa only [one_pow] using StaticBallL2.exterior_norm_bound 1 zero_lt_one i j z hz
    _ = V*((1/Real.pi)*‖z‖⁻¹^3) := by rw [hv]; field_simp; ring

def horizontal (y : Space) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1]

theorem horizontal_distance (q : Plane) (y : Space) :
    ‖q-horizontal y‖ ≤ ‖MaxwellPlaneTail.planePoint q-y‖ := by
  have hs : ‖q-horizontal y‖^2 ≤ ‖MaxwellPlaneTail.planePoint q-y‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_three]
    simp [horizontal, MaxwellPlaneTail.planePoint, Real.norm_eq_abs]
    exact sq_nonneg (y 2)
  nlinarith [norm_nonneg (q-horizontal y), norm_nonneg (MaxwellPlaneTail.planePoint q-y)]

theorem kernel_envelope (d : ℝ) (hd : 0 < d) (y : Space) (hy : d ≤ |y 2|)
    (q : Plane) (i j : Fin 3) :
    ‖GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j‖ ≤
      (1/Real.pi)*envelope d (q-horizontal y) := by
  have hdr := PlaneSourceKernel.gap_distance d q y hy
  have hn : MaxwellPlaneTail.planePoint q-y ≠ 0 := norm_pos_iff.mp (hd.trans_le hdr)
  exact (static_hessian_bound _ hn i j).trans
    (mul_le_mul_of_nonneg_left
      (inverse_cube_le_envelope d hd (q-horizontal y) _ hdr (horizontal_distance q y))
      (by positivity))

theorem translated_envelope_integrable (d : ℝ) (hd : 0 < d) (p : Plane) :
    Integrable (fun q => envelope d (q-p)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure Plane) (-p)).integrable_comp
      (envelope_integrable d hd).aestronglyMeasurable |>.mpr (envelope_integrable d hd)

theorem translated_envelope_integral (d : ℝ) (hd : 0 < d) (p : Plane) :
    (∫ q : Plane, envelope d (q-p)) = (Real.pi+diskConstant)/d := by
  rw [show (∫ q : Plane, envelope d (q-p)) = ∫ q : Plane, envelope d q by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (envelope d) (-p)]
  exact envelope_integral d hd

theorem hessian_measurable (i j : Fin 3) :
    Measurable (fun z : Space => GreenKernel.phiHessian 0 z i j) := by
  unfold GreenKernel.phiHessian GreenKernel.radialD GreenKernel.radialDD
  fun_prop

theorem plane_kernel_integrable (d : ℝ) (hd : 0 < d) (y : Space) (hy : d ≤ |y 2|)
    (i j : Fin 3) :
    Integrable (fun q : Plane => GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j) := by
  apply ((translated_envelope_integrable d hd (horizontal y)).const_mul (1/Real.pi)).mono'
    ((hessian_measurable i j).comp
      (MaxwellPlaneTail.planePoint_continuous.sub continuous_const).measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => kernel_envelope d hd y hy q i j)

theorem plane_kernel_mass (d : ℝ) (hd : 0 < d) (y : Space) (hy : d ≤ |y 2|)
    (i j : Fin 3) :
    (∫ q : Plane, ‖GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j‖) ≤ 3/d := by
  have hc : diskConstant = 2*Real.pi := by
    simp [diskConstant, measureReal_def, ENNReal.toReal_ofReal Real.pi_pos.le]
  calc
    _ ≤ ∫ q : Plane, (1/Real.pi)*envelope d (q-horizontal y) := by
      exact integral_mono_ae (plane_kernel_integrable d hd y hy i j).norm
        ((translated_envelope_integrable d hd (horizontal y)).const_mul (1/Real.pi))
        (Filter.Eventually.of_forall (fun q => kernel_envelope d hd y hy q i j))
    _ = 3/d := by
      rw [integral_const_mul, translated_envelope_integral d hd, hc]
      field_simp
      ring

end OQ14.StaticPlaneKernel

#print axioms OQ14.StaticPlaneKernel.envelope_integrable
#print axioms OQ14.StaticPlaneKernel.envelope_nonnegative
#print axioms OQ14.StaticPlaneKernel.envelope_integral
#print axioms OQ14.StaticPlaneKernel.inverse_cube_le_envelope
#print axioms OQ14.StaticPlaneKernel.static_hessian_bound
#print axioms OQ14.StaticPlaneKernel.horizontal_distance
#print axioms OQ14.StaticPlaneKernel.kernel_envelope
#print axioms OQ14.StaticPlaneKernel.translated_envelope_integrable
#print axioms OQ14.StaticPlaneKernel.translated_envelope_integral
#print axioms OQ14.StaticPlaneKernel.hessian_measurable
#print axioms OQ14.StaticPlaneKernel.plane_kernel_integrable
#print axioms OQ14.StaticPlaneKernel.plane_kernel_mass

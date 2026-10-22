import SphereCapH1
import KernelIntegrability

/-! Literal conical potential and electric candidate, with actual Borel representatives and local bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalCapField
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology InnerProductSpace ENNReal

def unit (x : Space) : Sphere := ⟨if x = 0 then basis 2 else ‖x‖⁻¹ • x,by
  rw [mem_sphere,dist_zero_right]
  split_ifs with hx
  · simp [basis]
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem unit_measurable : Measurable unit := by
  apply Measurable.subtype_mk
  exact measurable_const.piecewise (measurableSet_singleton (0 : Space))
    (continuous_norm.measurable.inv.smul measurable_id)

theorem unit_polar (r : ℝ) (hr : 0 < r) (n : Sphere) : unit (r • (n : Space)) = n := by
  apply Subtype.ext
  have hn : ‖r • (n : Space)‖ = r := by simp [norm_smul,sphere_norm,abs_of_pos hr]
  have hx : r • (n : Space) ≠ 0 := by intro h; rw [h,norm_zero] at hn; linarith
  change (if r • (n : Space) = 0 then basis 2 else ‖r • (n : Space)‖⁻¹ • r • (n : Space)) = _
  rw [if_neg hx,hn,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

def borelSlope (a t z : ℝ) : ℝ :=
  if z < -t then deriv (negative a t) z else
    if z ≤ t then deriv (CapAngularShooting.interior a t) z else deriv (exterior a t) z

theorem borelSlope_measurable (a t : ℝ) : Measurable (borelSlope a t) := by
  exact (measurable_deriv _).piecewise measurableSet_Iio
    ((measurable_deriv _).piecewise measurableSet_Iic (measurable_deriv _))

theorem borelSlope_eq (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    borelSlope a t z = CapSturmLiouville.slope a t z := by
  by_cases hL : z < -t
  · simp only [borelSlope,CapSturmLiouville.slope,if_pos hL]
    exact (negative_hasDerivAt a t z ha (left_argument t z ht ht1 ⟨hz.1,hL.le⟩)).deriv
  · by_cases hM : z ≤ t
    · simp only [borelSlope,CapSturmLiouville.slope,if_neg hL,if_pos hM]
      exact (interior_hasDerivAt a t z ha (middle_argument t z ht1 ⟨le_of_not_gt hL,hM⟩)).deriv
    · simp only [borelSlope,CapSturmLiouville.slope,if_neg hL,if_neg hM]
      exact (exterior_hasDerivAt a t z ha (right_argument t z ht ht1 ⟨le_of_not_ge hM,hz.2⟩)).deriv

theorem gradient_measurable (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (SphereCapH1.gradient a t) := by
  have hs : (fun n : Sphere => borelSlope a t ((n : Space) 2)) =
      fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2) :=
    funext (fun n => borelSlope_eq a t _ ha ht ht1 (SphereCapWeak.coordinate_range n))
  have hm := (borelSlope_measurable a t).comp
    (OQ14.ConicalAngularTrial.coordinate_continuous 2).measurable
  change Measurable (fun n : Sphere => borelSlope a t ((n : Space) 2)) at hm
  rw [hs] at hm
  exact hm.smul (continuous_const.sub
    ((OQ14.ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val)).measurable

def angularElectric (ν a t : ℝ) (n : Sphere) : Space :=
  (ν*field a t n) • (n : Space)+SphereCapH1.gradient a t n
def potential (ν a t : ℝ) (x : Space) : ℝ := ‖x‖^ν*field a t (unit x)
def electric (ν a t : ℝ) (x : Space) : Space :=
  if x = 0 then 0 else ‖x‖^(ν-1) • angularElectric ν a t (unit x)
def permittivity (d t : ℝ) (x : Space) : ℝ := coefficient d t ((unit x : Space) 2)

theorem potential_polar (ν a t r : ℝ) (hr : 0 < r) (n : Sphere) :
    potential ν a t (r • (n : Space)) = r^ν*field a t n := by
  simp [potential,norm_smul,sphere_norm,abs_of_pos hr,unit_polar r hr n]

theorem electric_polar (ν a t r : ℝ) (hr : 0 < r) (n : Sphere) :
    electric ν a t (r • (n : Space)) = r^(ν-1) • angularElectric ν a t n := by
  have hx : r • (n : Space) ≠ 0 := by
    have hn : ‖r • (n : Space)‖ = r := by simp [norm_smul,sphere_norm,abs_of_pos hr]
    intro h; rw [h,norm_zero] at hn; linarith
  simp [electric,hx,norm_smul,sphere_norm,abs_of_pos hr,unit_polar r hr n]

theorem permittivity_polar (d t r : ℝ) (hr : 0 < r) (n : Sphere) :
    permittivity d t (r • (n : Space)) = coefficient d t ((n : Space) 2) := by
  rw [permittivity,unit_polar r hr n]

theorem angularElectric_norm_sq (ν a t : ℝ) (n : Sphere) :
    ‖angularElectric ν a t n‖^2 = ν^2*field a t n^2+‖SphereCapH1.gradient a t n‖^2 := by
  rw [angularElectric,norm_add_sq_real,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one,
    sq_abs,inner_smul_left,gradient_tangent,mul_zero,mul_zero,add_zero]
  ring

theorem angularElectric_measurable (ν a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : Measurable (angularElectric ν a t) := by
  exact ((measurable_const.mul (SphereCapWeak.profile_continuous a t ha ht ht1).measurable).smul
    measurable_subtype_coe).add (gradient_measurable a t ha ht ht1)

theorem potential_measurable (ν a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (potential ν a t) :=
  (continuous_norm.measurable.pow_const ν).mul
    ((SphereCapWeak.profile_continuous a t ha ht ht1).measurable.comp unit_measurable)

theorem electric_measurable (ν a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (electric ν a t) := by
  exact measurable_const.piecewise (measurableSet_singleton (0 : Space))
    ((continuous_norm.measurable.pow_const (ν-1)).smul
      ((angularElectric_measurable ν a t ha ht ht1).comp unit_measurable))

theorem electric_zero (ν a t : ℝ) : electric ν a t 0 = 0 := by simp [electric]

theorem potential_zero (ν a t : ℝ) (hν : 0 < ν) : potential ν a t 0 = 0 := by
  simp [potential,Real.zero_rpow hν.ne']

theorem angular_bounds (ν a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ n : Sphere, ‖field a t n‖ ≤ C ∧ ‖angularElectric ν a t n‖ ≤ C := by
  obtain ⟨CF,hCF⟩ := isCompact_univ.exists_bound_of_continuousOn
    (SphereCapWeak.profile_continuous a t ha ht ht1).continuousOn
  obtain ⟨CG,hCG,hbG⟩ := SphereCapWeak.slope_bound a t ha ht ht1
  have hφ (n : Sphere) : ‖field a t n‖ ≤ |CF| := (hCF n (mem_univ n)).trans (le_abs_self CF)
  have hG (n : Sphere) : ‖SphereCapH1.gradient a t n‖ ≤ CG := by
    calc
      ‖SphereCapH1.gradient a t n‖ = ‖CapSturmLiouville.slope a t ((n : Space) 2)‖*
        ‖basis 2-(n : Space) 2 • (n : Space)‖ := norm_smul _ _
      _ ≤ CG*1 := mul_le_mul (hbG _ (SphereCapWeak.coordinate_range n))
        (tangent_norm_le n) (norm_nonneg _) hCG
      _ = CG := mul_one _
  refine ⟨|CF|+|ν| * |CF|+CG,by positivity,fun n => ⟨?_,?_⟩⟩
  · exact (hφ n).trans (by linarith [mul_nonneg (abs_nonneg ν) (abs_nonneg CF)])
  · calc
      ‖angularElectric ν a t n‖ ≤ ‖(ν*field a t n) • (n : Space)‖+‖SphereCapH1.gradient a t n‖ := norm_add_le _ _
      _ ≤ |ν| * |CF|+CG := by
        rw [norm_smul,sphere_norm,mul_one,norm_mul,Real.norm_eq_abs]
        exact add_le_add (mul_le_mul_of_nonneg_left (hφ n) (abs_nonneg ν)) (hG n)
      _ ≤ |CF|+|ν| * |CF|+CG := by linarith [abs_nonneg CF]

theorem potential_bound_ball (ν a t R : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ x ∈ closedBall (0 : Space) R, ‖potential ν a t x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := angular_bounds ν a t ha ht ht1
  refine ⟨(max R 1)^ν*C,by positivity,fun x hx => ?_⟩
  have hR : ‖x‖ ≤ max R 1 := (mem_closedBall_zero_iff.mp hx).trans (le_max_left _ _)
  calc
    ‖potential ν a t x‖ = ‖x‖^ν*‖field a t (unit x)‖ := by
      rw [potential,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    _ ≤ (max R 1)^ν*C := mul_le_mul
      (Real.rpow_le_rpow (norm_nonneg _) hR hν) (hb (unit x)).1 (norm_nonneg _) (by positivity)

theorem electric_bound_ball (ν a t R : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ x ∈ closedBall (0 : Space) R, ‖electric ν a t x‖ ≤ C*‖x‖⁻¹ := by
  obtain ⟨C,hC,hb⟩ := angular_bounds ν a t ha ht ht1
  refine ⟨(max R 1)^ν*C,by positivity,fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst x
    simp [electric_zero]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hR : ‖x‖ ≤ max R 1 := (mem_closedBall_zero_iff.mp hx).trans (le_max_left _ _)
  calc
    ‖electric ν a t x‖ = ‖x‖^(ν-1)*‖angularElectric ν a t (unit x)‖ := by
      rw [electric,if_neg hx0,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp.le _)]
    _ ≤ ‖x‖^(ν-1)*C := mul_le_mul_of_nonneg_left (hb (unit x)).2 (Real.rpow_nonneg hp.le _)
    _ = (‖x‖^ν*C)*‖x‖⁻¹ := by rw [Real.rpow_sub hp,Real.rpow_one]; ring
    _ ≤ ((max R 1)^ν*C)*‖x‖⁻¹ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp.le hR hν) hC) (inv_nonneg.mpr hp.le)

theorem potential_memLp_two_ball (ν a t R : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : MemLp (potential ν a t) 2 (volume.restrict (closedBall 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space) R).measure_ne_top
  obtain ⟨C,_,hC⟩ := potential_bound_ball ν a t R hν ha ht ht1
  apply MemLp.of_bound (potential_measurable ν a t ha ht ht1).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hC x hx

theorem electric_memLp_two_ball (ν a t R : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : MemLp (electric ν a t) 2 (volume.restrict (closedBall 0 R)) := by
  have hm : Measurable (fun x : Space => ‖x‖⁻¹) := continuous_norm.measurable.inv
  have hi : MemLp (fun x : Space => ‖x‖⁻¹) 2 (volume.restrict (closedBall 0 R)) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs,sq_abs] using KernelIntegrability.inverse_norm_sq_integrable_ball R
  obtain ⟨C,_,hC⟩ := electric_bound_ball ν a t R hν ha ht ht1
  apply hi.of_le_mul (electric_measurable ν a t ha ht ht1).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  simpa only [Real.norm_eq_abs,abs_inv,abs_norm] using hC x hx

theorem potential_continuousAt_zero (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : ContinuousAt (potential ν a t) 0 := by
  obtain ⟨C,_,hC⟩ := angular_bounds ν a t ha ht ht1
  have hb (x : Space) : ‖potential ν a t x‖ ≤ C*‖x‖^ν := by
    rw [potential,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC (unit x)).1 (Real.rpow_nonneg (norm_nonneg x) ν)
  have hc : Continuous (fun x : Space => C*‖x‖^ν) :=
    continuous_const.mul ((Real.continuous_rpow_const hν.le).comp continuous_norm)
  have hl : Filter.Tendsto (fun x : Space => C*‖x‖^ν) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,Real.zero_rpow hν.ne',mul_zero] using hc.tendsto (0 : Space)
  rw [ContinuousAt,potential_zero ν a t hν]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun x => norm_nonneg _) hb hl)

theorem angularElectric_north_nonzero (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : 0 < ‖angularElectric ν a t north‖ := by
  have hs := angularElectric_norm_sq ν a t north
  have hp := field_nonzero a t ha ht ht1
  have hmul : 0 < ν*field a t north := mul_pos hν hp
  nlinarith [norm_nonneg (angularElectric ν a t north),sq_pos_of_pos hmul,
    sq_nonneg ‖SphereCapH1.gradient a t north‖]

end OQ14.ConicalCapField

#print axioms OQ14.ConicalCapField.unit_measurable
#print axioms OQ14.ConicalCapField.unit_polar
#print axioms OQ14.ConicalCapField.borelSlope_measurable
#print axioms OQ14.ConicalCapField.borelSlope_eq
#print axioms OQ14.ConicalCapField.gradient_measurable
#print axioms OQ14.ConicalCapField.potential_polar
#print axioms OQ14.ConicalCapField.electric_polar
#print axioms OQ14.ConicalCapField.permittivity_polar
#print axioms OQ14.ConicalCapField.angularElectric_norm_sq
#print axioms OQ14.ConicalCapField.angularElectric_measurable
#print axioms OQ14.ConicalCapField.potential_measurable
#print axioms OQ14.ConicalCapField.electric_measurable
#print axioms OQ14.ConicalCapField.electric_zero
#print axioms OQ14.ConicalCapField.potential_zero
#print axioms OQ14.ConicalCapField.angular_bounds
#print axioms OQ14.ConicalCapField.potential_bound_ball
#print axioms OQ14.ConicalCapField.electric_bound_ball
#print axioms OQ14.ConicalCapField.potential_memLp_two_ball
#print axioms OQ14.ConicalCapField.electric_memLp_two_ball
#print axioms OQ14.ConicalCapField.potential_continuousAt_zero
#print axioms OQ14.ConicalCapField.angularElectric_north_nonzero

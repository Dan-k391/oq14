import RiccatiOriginSeries

/-! # Actual regular Riccati normalization and derivative limits at the origin -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.RiccatiOriginLimits

open Complex Filter Set Metric OQ14.RiccatiSeriesCoefficients OQ14.RiccatiOriginSeries
open OQ14.HankelRealBasis
open scoped Topology

def normalized (l : ℕ) (z : ℂ) : ℂ := ∑' m, (coeff l m : ℂ)*z^(2*m)
def normalizedSlope (l : ℕ) (z : ℂ) : ℂ :=
  ∑' m, (coeff l m : ℂ)*(l+1+2*m : ℕ)*z^(2*m)

theorem evenSum_continuousAt_zero (a : ℕ → ℂ) (u : ℕ → ℝ) (hu : Summable u)
    (ha : ∀ m, ‖a m‖ ≤ u m) : ContinuousAt (fun z : ℂ => ∑' m, a m*z^(2*m)) 0 := by
  have hc : ContinuousOn (fun z : ℂ => ∑' m, a m*z^(2*m)) (ball 0 1) := by
    apply continuousOn_tsum (u := u)
      (fun m => (continuous_const.mul (continuous_id.pow (2*m))).continuousOn) hu
    intro m z hz
    rw [norm_mul,norm_pow]
    have hp : ‖z‖^(2*m) ≤ 1 := pow_le_one₀ (norm_nonneg z) (mem_ball_zero_iff.mp hz).le
    exact (mul_le_mul (ha m) hp (pow_nonneg (norm_nonneg z) _) ((norm_nonneg _).trans (ha m))).trans_eq
      (mul_one _)
  exact hc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))

theorem amplitudes_summable (l : ℕ) : Summable (fun m => amplitude l m) := by
  apply Summable.of_nonneg_of_le (fun m => (amplitude_pos l m).le)
    (fun m => ?_) ((Real.summable_pow_div_factorial (1/2)).mul_left (amplitude l 0))
  simpa only [one_pow,mul_one,one_div] using power_majorant l m 1 zero_le_one

theorem slopes_summable (l : ℕ) : Summable (fun m => amplitude l m*(l+1+2*m)) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (amplitude_pos l m).le (by positivity))
    (fun m => ?_) ((Real.summable_pow_div_factorial 1).mul_left (amplitude l 0*(l+2)))
  simpa only [one_pow,mul_one] using derivative_power_majorant l m 1 zero_le_one

theorem normalized_continuousAt_zero (l : ℕ) : ContinuousAt (normalized l) 0 := by
  exact evenSum_continuousAt_zero _ _ (amplitudes_summable l)
    (fun m => by simp only [Complex.norm_real,Real.norm_eq_abs,coeff_abs,le_refl])

theorem normalizedSlope_continuousAt_zero (l : ℕ) : ContinuousAt (normalizedSlope l) 0 := by
  exact evenSum_continuousAt_zero _ _ (slopes_summable l)
    (fun m => by simpa only [termD,one_pow,mul_one,norm_one] using (termD_norm l m 1).le)

theorem normalized_zero (l : ℕ) : normalized l 0 = (amplitude l 0 : ℂ) := by
  unfold normalized
  rw [tsum_eq_single 0]
  · simp [coeff]
  · intro m hm
    rw [zero_pow (by omega : 2*m ≠ 0),mul_zero]

theorem normalizedSlope_zero (l : ℕ) :
    normalizedSlope l 0 = ((l+1)*amplitude l 0 : ℝ) := by
  unfold normalizedSlope
  rw [tsum_eq_single 0]
  · simp [coeff]
    ring
  · intro m hm
    rw [zero_pow (by omega : 2*m ≠ 0),mul_zero]

theorem origin_factor (l : ℕ) (z : ℂ) : origin l z = z^(l+1)*normalized l z := by
  rw [origin,normalized,← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [term,pow_add]
  ring

theorem originD_factor (l : ℕ) (z : ℂ) : originD l z = z^l*normalizedSlope l z := by
  rw [originD,normalizedSlope,← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [termD,pow_add]
  ring

theorem regular_factor (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    regular l r = r^(l+1)*(normalized l (r : ℂ)).re := by
  have h := congrArg Complex.re (origin_factor l (r : ℂ))
  rw [origin_eq_psi l _ (Complex.ofReal_ne_zero.mpr hr),← regular_eq_psi] at h
  simpa only [Complex.ofReal_re,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_im,
    zero_mul,sub_zero] using h

theorem regularD_factor (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    regularD l r = r^l*(normalizedSlope l (r : ℂ)).re := by
  have h := congrArg Complex.re (originD_factor l (r : ℂ))
  rw [originD_eq_psiD l _ (Complex.ofReal_ne_zero.mpr hr),← regularD_eq_psiD] at h
  simpa only [Complex.ofReal_re,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_im,
    zero_mul,sub_zero] using h

theorem regular_scaled_limit (l : ℕ) :
    Tendsto (fun r : ℝ => regular l r/r^(l+1)) (𝓝[>] 0) (𝓝 (amplitude l 0)) := by
  have hc : ContinuousAt (fun t : ℝ => normalized l (t : ℂ)) 0 :=
    (normalized_continuousAt_zero l).comp (f := Complex.ofReal) (x := (0 : ℝ))
      Complex.continuous_ofReal.continuousAt
  have h := (Complex.continuous_re.continuousAt.comp hc).tendsto
  dsimp only [Function.comp_def,Complex.ofReal_zero] at h
  rw [normalized_zero,Complex.ofReal_re] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [hp] with r hr
  rw [regular_factor l r hr.ne']
  field_simp [hr.ne']

theorem regularD_scaled_limit (l : ℕ) :
    Tendsto (fun r : ℝ => regularD l r/r^l) (𝓝[>] 0) (𝓝 ((l+1)*amplitude l 0)) := by
  have hc : ContinuousAt (fun t : ℝ => normalizedSlope l (t : ℂ)) 0 :=
    (normalizedSlope_continuousAt_zero l).comp (f := Complex.ofReal) (x := (0 : ℝ))
      Complex.continuous_ofReal.continuousAt
  have h := (Complex.continuous_re.continuousAt.comp hc).tendsto
  dsimp only [Function.comp_def,Complex.ofReal_zero] at h
  rw [normalizedSlope_zero,Complex.ofReal_re] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [hp] with r hr
  rw [regularD_factor l r hr.ne']
  field_simp [hr.ne']

theorem eventually_regular_positive (l : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < regular l r ∧ 0 < regularD l r := by
  have hu := (regular_scaled_limit l).eventually (lt_mem_nhds (amplitude_pos l 0))
  have hdu := (regularD_scaled_limit l).eventually
    (lt_mem_nhds (mul_pos (by positivity : (0 : ℝ) < l+1) (amplitude_pos l 0)))
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [hu,hdu,hp] with r hu hdu hr
  exact ⟨(div_pos_iff_of_pos_right (pow_pos hr _)).mp hu,
    (div_pos_iff_of_pos_right (pow_pos hr _)).mp hdu⟩

end OQ14.RiccatiOriginLimits

#print axioms OQ14.RiccatiOriginLimits.evenSum_continuousAt_zero
#print axioms OQ14.RiccatiOriginLimits.amplitudes_summable
#print axioms OQ14.RiccatiOriginLimits.slopes_summable
#print axioms OQ14.RiccatiOriginLimits.normalized_continuousAt_zero
#print axioms OQ14.RiccatiOriginLimits.normalizedSlope_continuousAt_zero
#print axioms OQ14.RiccatiOriginLimits.normalized_zero
#print axioms OQ14.RiccatiOriginLimits.normalizedSlope_zero
#print axioms OQ14.RiccatiOriginLimits.origin_factor
#print axioms OQ14.RiccatiOriginLimits.originD_factor
#print axioms OQ14.RiccatiOriginLimits.regular_factor
#print axioms OQ14.RiccatiOriginLimits.regularD_factor
#print axioms OQ14.RiccatiOriginLimits.regular_scaled_limit
#print axioms OQ14.RiccatiOriginLimits.regularD_scaled_limit
#print axioms OQ14.RiccatiOriginLimits.eventually_regular_positive

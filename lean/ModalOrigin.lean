import ModalInterface
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Removable center of the actual regular dipole

Repeated divided differences of the exponential construct the regular radial
profile without an assumed asymptotic expansion.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.ModalOrigin

open Complex Filter Asymptotics OQ14.Maxwell OQ14.GreenKernel
  OQ14.ModalAlgebra OQ14.ModalDipole OQ14.ModalInterface
open scoped Topology

def expTail (m : ℕ) : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[m] Complex.exp

theorem expTail_series (m : ℕ) :
    HasFPowerSeriesAt (expTail m)
      (FormalMultilinearSeries.fslope^[m] (NormedSpace.expSeries ℂ ℂ)) 0 := by
  apply HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.exp_hasFPowerSeriesAt_zero

theorem expTail_zero (m : ℕ) : expTail m 0 = (Nat.factorial m : ℂ)⁻¹ := by
  rw [← (expTail_series m).coeff_zero 1]
  change (FormalMultilinearSeries.fslope^[m] (NormedSpace.expSeries ℂ ℂ)).coeff 0 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope]
  rw [Nat.zero_add]
  simp only [FormalMultilinearSeries.coeff]
  change NormedSpace.expSeries ℂ ℂ m (fun _ => 1) = _
  rw [NormedSpace.expSeries_apply_eq]
  simp

theorem expTail_differentiable (m : ℕ) : Differentiable ℂ (expTail m) := by
  induction m with
  | zero => exact Complex.differentiable_exp
  | succ m ih =>
    simp only [expTail, Function.iterate_succ_apply']
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr ih.differentiableOn

theorem expTail_step (m : ℕ) (z : ℂ) :
    z * expTail (m+1) z = expTail m z - (Nat.factorial m : ℂ)⁻¹ := by
  rw [expTail, Function.iterate_succ_apply']
  simpa [expTail_zero] using sub_smul_dslope (expTail m) 0 z

def profile (z : ℂ) : ℂ :=
  (expTail 2 (I*z) + expTail 2 (-I*z) -
    expTail 3 (I*z) - expTail 3 (-I*z)) / 2

theorem profile_differentiable : Differentiable ℂ profile := by
  unfold profile
  exact ((((expTail_differentiable 2).comp ((differentiable_const I).mul differentiable_id)).add
    ((expTail_differentiable 2).comp ((differentiable_const (-I)).mul differentiable_id))).sub
    ((expTail_differentiable 3).comp ((differentiable_const I).mul differentiable_id)) |>.sub
    ((expTail_differentiable 3).comp ((differentiable_const (-I)).mul differentiable_id))).div_const 2

theorem profile_zero : profile 0 = 1/3 := by
  norm_num [profile, expTail_zero, Nat.factorial]

theorem profile_hasDerivAt_zero : HasDerivAt profile 0 0 := by
  have hp (m : ℕ) := ((expTail_differentiable m (I*0)).hasDerivAt).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul I)
  have hm (m : ℕ) := ((expTail_differentiable m (-I*0)).hasDerivAt).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul (-I))
  convert (((hp 2).add (hm 2)).sub (hp 3) |>.sub (hm 3)).div_const 2 using 1
  simp only [mul_zero, mul_one]; ring

theorem expTail_two_identity (z : ℂ) :
    z^2 * expTail 2 z = exp z - 1 - z := by
  have h0 := expTail_step 0 z
  have h1 := expTail_step 1 z
  norm_num [expTail, Nat.factorial] at h0
  change z * expTail 1 z = exp z - 1 at h0
  norm_num [Nat.factorial] at h1
  linear_combination z*h1+h0

theorem expTail_three_identity (z : ℂ) :
    z^3 * expTail 3 z = exp z - 1 - z - z^2/2 := by
  have h2 := expTail_step 2 z
  have h1 := expTail_two_identity z
  norm_num [Nat.factorial] at h2
  linear_combination z^2*h2+h1

theorem psi_profile (z : ℂ) (hz : z ≠ 0) : psi 1 z = z^2 * profile z := by
  have hp2 := expTail_two_identity (I*z)
  have hm2 := expTail_two_identity (-I*z)
  have hp3 := expTail_three_identity (I*z)
  have hm3 := expTail_three_identity (-I*z)
  have he : z * psi 1 z =
      -((z+I)*exp (I*z)+(z-I)*exp (-I*z))/2 := by
    unfold psi xi xiMinus
    rw [p_one, pMinus_one]
    norm_num
    field_simp [hz]
    ring
  apply mul_left_cancel₀ hz
  rw [he]
  unfold profile
  norm_num [neg_mul, mul_pow, show I^3 = -I by rw [pow_succ, I_sq]; ring] at hp2 hm2 hp3 hm3
  simp only [neg_mul]
  linear_combination (norm := skip) z/2*hp2+z/2*hm2+I/2*hp3-I/2*hm3
  ring_nf
  norm_num [pow_succ, I_sq]

theorem psiD_profile (z : ℂ) (hz : z ≠ 0) :
    psiD 1 z = 2*z*profile z + z^2*deriv profile z := by
  have he : psi 1 =ᶠ[𝓝 z] fun w => w^2*profile w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw using psi_profile w hw
  have hd := ((hasDerivAt_id z).pow 2).mul (profile_differentiable z).hasDerivAt
  simpa using (he.hasDerivAt_iff.mp (psi_hasDerivAt 1 z hz)).unique hd

theorem radial_zero_derivative (f : ℂ → ℂ) (hf : HasDerivAt f 0 0) :
    HasFDerivAt (fun x : Space => f (‖x‖ : ℂ)) (0 : Space →L[ℝ] ℂ) 0 := by
  have ho : (fun z : ℂ => f z - f 0) =o[𝓝 0] fun z => z := by
    simpa using hasDerivAt_iff_isLittleO.mp hf
  have ht : Tendsto (fun x : Space => (‖x‖ : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (continuous_norm.continuousAt.tendsto (x := (0 : Space)))
  have hc := (ho.comp_tendsto ht).norm_right
  simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hc
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa using hc.of_norm_right

theorem continuous_mul_coordinate (f : Space → ℂ) (hf : ContinuousAt f 0) (j : Fin 3) :
    HasFDerivAt (fun x => f x * (x j : ℂ)) (f 0 • coordinate j) 0 := by
  have ht : Tendsto (fun x => f x - f 0) (𝓝 (0 : Space)) (𝓝 0) := by
    simpa using hf.tendsto.sub (tendsto_const_nhds (x := f 0))
  have hl : (fun x => f x - f 0) =o[𝓝 (0 : Space)] fun _ => (1 : ℂ) :=
    (isLittleO_one_iff ℂ).mpr ht
  have ho := hl.mul_isBigO (isBigO_refl (coordinate j) (𝓝 (0 : Space)))
  have ho' : (fun x : Space => (f x - f 0) * (x j : ℂ)) =o[𝓝 0] fun x => x :=
    (by simpa using ho : (fun x => (f x - f 0) * coordinate j x) =o[𝓝 0] coordinate j).trans_isBigO
      ((coordinate j).isBigO_comp id (𝓝 0))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa [sub_mul, coordinate] using ho'

theorem continuous_mul_two_coordinates (f : Space → ℂ) (hf : ContinuousAt f 0)
    (i j : Fin 3) :
    HasFDerivAt (fun x => f x * (x i : ℂ) * (x j : ℂ)) (0 : Space →L[ℝ] ℂ) 0 := by
  have hc := hf.mul (coordinate i).continuous.continuousAt
  have h := continuous_mul_coordinate (fun x => f x * (x i : ℂ)) hc j
  have he : f (0 : Space) * ((0 : Space) i : ℂ) = (0 : ℂ) := by simp
  rw [he] at h
  have hz : ((0 : ℂ) • coordinate j : Space →L[ℝ] ℂ) = 0 := by
    ext x
    simp
  rw [hz] at h
  exact h

def profileSlope : ℂ → ℂ := dslope (deriv profile) 0

theorem profile_deriv_differentiable : Differentiable ℂ (deriv profile) := by
  rw [← differentiableOn_univ]
  exact profile_differentiable.differentiableOn.deriv isOpen_univ

theorem profileSlope_differentiable : Differentiable ℂ profileSlope := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    profile_deriv_differentiable.differentiableOn

theorem profileSlope_identity (z : ℂ) : z * profileSlope z = deriv profile z := by
  have h := sub_smul_dslope (deriv profile) 0 z
  simpa [profileSlope, profile_hasDerivAt_zero.deriv] using h

def centerA (κ z : ℂ) : ℂ :=
  κ^2 * (2*profile (κ*z) + (κ*z)*deriv profile (κ*z))
def centerB (κ z : ℂ) : ℂ := -κ^4 * profileSlope (κ*z)
def centerC (κ k z : ℂ) : ℂ := (I*κ^4/k) * profile (κ*z)

def centerE (κ : ℂ) : Field :=
  axisField (fun r => centerA κ (r : ℂ)) (fun r => centerB κ (r : ℂ))
def centerH (κ k : ℂ) : Field :=
  swirlField (fun r => centerC κ k (r : ℂ))

theorem centerA_differentiable (κ : ℂ) : Differentiable ℂ (centerA κ) := by
  unfold centerA
  exact ((profile_differentiable.comp ((differentiable_const κ).mul differentiable_id) |>.const_mul 2).add
    (((differentiable_const κ).mul differentiable_id).mul
      (profile_deriv_differentiable.comp ((differentiable_const κ).mul differentiable_id)))).const_mul _

theorem centerB_differentiable (κ : ℂ) : Differentiable ℂ (centerB κ) :=
  (profileSlope_differentiable.comp ((differentiable_const κ).mul differentiable_id)).const_mul _

theorem centerC_differentiable (κ k : ℂ) : Differentiable ℂ (centerC κ k) :=
  (profile_differentiable.comp ((differentiable_const κ).mul differentiable_id)).const_mul _

theorem centerA_zero (κ : ℂ) : centerA κ 0 = 2*κ^2/3 := by
  simp [centerA, profile_zero]; ring

theorem centerC_zero (κ k : ℂ) : centerC κ k 0 = I*κ^4/(3*k) := by
  simp [centerC, profile_zero]; ring

theorem centerA_hasDerivAt_zero (κ : ℂ) : HasDerivAt (centerA κ) 0 0 := by
  have hp : HasDerivAt (fun z : ℂ => profile (κ*z)) 0 0 := by
    have hpp : HasDerivAt profile 0 (κ*0) := by simpa using profile_hasDerivAt_zero
    simpa using hpp.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul κ)
  have hd := ((profile_deriv_differentiable (κ*0)).hasDerivAt).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul κ)
  convert ((hp.const_mul 2).add (((hasDerivAt_id (0 : ℂ)).const_mul κ).mul hd)).const_mul (κ^2) using 1
  simp [profile_hasDerivAt_zero.deriv]

theorem centerA_eq (κ : ℂ) (hκ : κ ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    centerA κ (r : ℂ) = electricA (scaledRadialD (psiD 1) κ) r := by
  have hr' := ofReal_ne_zero.mpr hr
  unfold centerA electricA scaledRadialD
  rw [psiD_profile _ (mul_ne_zero hκ hr')]
  field_simp [hr']
  ring

theorem centerB_eq (κ : ℂ) (hκ : κ ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    centerB κ (r : ℂ) =
      electricB (scaledRadial (psi 1) κ) (scaledRadialD (psiD 1) κ) r := by
  have hr' := ofReal_ne_zero.mpr hr
  have hz := mul_ne_zero hκ hr'
  have hj : profileSlope (κ*r) = deriv profile (κ*r)/(κ*r) :=
    (eq_div_iff hz).mpr (by simpa only [mul_comm] using profileSlope_identity (κ*r))
  unfold centerB electricB scaledRadial scaledRadialD
  rw [hj, psi_profile _ hz, psiD_profile _ hz]
  field_simp [hr', hκ]
  ring

theorem centerC_eq (κ k : ℂ) (hκ : κ ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    centerC κ k (r : ℂ) = magneticC κ k (scaledRadial (psi 1) κ) r := by
  have hr' := ofReal_ne_zero.mpr hr
  unfold centerC magneticC scaledRadial
  rw [psi_profile _ (mul_ne_zero hκ hr')]
  by_cases hk : k = 0
  · simp [hk]
  · field_simp [hr', hk]
    ring

theorem centerE_eq_regular (κ : ℂ) (hκ : κ ≠ 0) (x : Space) (hx : x ≠ 0) :
    centerE κ x = regularE κ x := by
  have hr := norm_ne_zero_iff.mpr hx
  simp only [centerE, regularE, dipoleE, axisField, centerA_eq κ hκ _ hr,
    centerB_eq κ hκ _ hr]

theorem centerH_eq_regular (κ k : ℂ) (hκ : κ ≠ 0) (x : Space) (hx : x ≠ 0) :
    centerH κ k x = regularH κ k x := by
  have hr := norm_ne_zero_iff.mpr hx
  simp only [centerH, regularH, dipoleH, swirlField, centerC_eq κ k hκ _ hr]

theorem centerE_hasFDerivAt_zero (κ : ℂ) (j : Fin 3) :
    HasFDerivAt (fun x => centerE κ x j) (0 : Space →L[ℝ] ℂ) 0 := by
  have ha := radial_zero_derivative (centerA κ) (centerA_hasDerivAt_zero κ)
  have hb : ContinuousAt (fun x : Space => centerB κ (‖x‖ : ℂ)) 0 :=
    ((centerB_differentiable κ).continuous.comp
      (Complex.continuous_ofReal.comp continuous_norm)).continuousAt
  fin_cases j
  · exact continuous_mul_two_coordinates _ hb 2 0
  · exact continuous_mul_two_coordinates _ hb 2 1
  · simpa using ha.add (continuous_mul_two_coordinates _ hb 2 2)

theorem centerE_zero (κ : ℂ) : centerE κ 0 = ![0,0,2*κ^2/3] := by
  simp [centerE, axisField, centerA_zero]

theorem centerH_zero (κ k : ℂ) : centerH κ k 0 = 0 := by
  ext j
  fin_cases j <;> simp [centerH, swirlField]

theorem centerE_curl_zero (κ : ℂ) : curl (centerE κ) 0 = 0 := by
  ext j
  fin_cases j <;> simp [curl, pd, dcoord, (centerE_hasFDerivAt_zero κ _).fderiv]

theorem centerH_curl_zero (κ k : ℂ) :
    curl (centerH κ k) 0 = ![0,0,-2*I*κ^4/(3*k)] := by
  have hc : ContinuousAt (fun x : Space => centerC κ k (‖x‖ : ℂ)) 0 :=
    ((centerC_differentiable κ k).continuous.comp
      (Complex.continuous_ofReal.comp continuous_norm)).continuousAt
  have h0 := continuous_mul_coordinate _ hc 1
  have h1 := (continuous_mul_coordinate _ hc 0).neg
  have h2 := hasFDerivAt_const (𝕜 := ℝ) (0 : Space) (0 : ℂ)
  have he0 : (fun x => centerH κ k x 0) = fun x => centerC κ k (‖x‖ : ℂ)*(x 1 : ℂ) := rfl
  have he1 : (fun x => centerH κ k x 1) = fun x => -(centerC κ k (‖x‖ : ℂ)*(x 0 : ℂ)) := by
    funext x; simp [centerH, swirlField]
  have he2 : (fun x => centerH κ k x 2) = fun _ => (0 : ℂ) := rfl
  ext j
  fin_cases j <;>
    simp [curl, pd, dcoord, he0, he1, he2, h0.fderiv, h1.fderiv, h2.fderiv,
      coordinate, basis, EuclideanSpace.single_apply, centerC_zero]
  ring

theorem center_maxwell_zero (κ k ε : ℂ) (hk : k ≠ 0) (hκ : κ^2 = k^2*ε) :
    ComplexMaxwellAt k ε (centerE κ) (centerH κ k) 0 := by
  constructor
  · rw [centerE_curl_zero, centerH_zero]
    ext j
    simp
  · rw [centerH_curl_zero, centerE_zero]
    ext j
    fin_cases j <;> simp
    have h4 : κ^4 = κ^2*k^2*ε := by
      calc
        κ^4 = κ^2*κ^2 := by ring
        _ = κ^2*(k^2*ε) := by rw [hκ]
        _ = _ := by ring
    rw [h4]
    field_simp [hk]
    ring

theorem curl_eventuallyEq (E F : Field) (x : Space) (h : E =ᶠ[𝓝 x] F) :
    curl E x = curl F x := by
  have hd (j : Fin 3) : fderiv ℝ (fun y => E y j) x = fderiv ℝ (fun y => F y j) x :=
    (h.fun_comp (fun v => v j)).fderiv_eq
  simp only [curl, pd, dcoord, hd]

theorem center_maxwell (κ k ε : ℂ) (hκ0 : κ ≠ 0) (hk : k ≠ 0)
    (hκ : κ^2 = k^2*ε) (x : Space) :
    ComplexMaxwellAt k ε (centerE κ) (centerH κ k) x := by
  by_cases hx : x = 0
  · subst x
    exact center_maxwell_zero κ k ε hk hκ
  have he : centerE κ =ᶠ[𝓝 x] regularE κ := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy using centerE_eq_regular κ hκ0 y hy
  have hh : centerH κ k =ᶠ[𝓝 x] regularH κ k := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy using centerH_eq_regular κ k hκ0 y hy
  have hm := regular_dipole_maxwell κ k ε hκ0 hk hκ x hx
  constructor
  · rw [curl_eventuallyEq _ _ x he, hm.1, centerH_eq_regular κ k hκ0 x hx]
  · rw [curl_eventuallyEq _ _ x hh, hm.2, centerE_eq_regular κ hκ0 x hx]

theorem centerE_continuous (κ : ℂ) (j : Fin 3) :
    Continuous (fun x => centerE κ x j) := by
  have ha := (centerA_differentiable κ).continuous.comp
    (Complex.continuous_ofReal.comp (continuous_norm : Continuous (fun x : Space => ‖x‖)))
  have hb := (centerB_differentiable κ).continuous.comp
    (Complex.continuous_ofReal.comp (continuous_norm : Continuous (fun x : Space => ‖x‖)))
  fin_cases j
  · exact (hb.mul (coordinate 2).continuous).mul (coordinate 0).continuous
  · exact (hb.mul (coordinate 2).continuous).mul (coordinate 1).continuous
  · exact ha.add ((hb.mul (coordinate 2).continuous).mul (coordinate 2).continuous)

theorem centerH_continuous (κ k : ℂ) (j : Fin 3) :
    Continuous (fun x => centerH κ k x j) := by
  have hc := (centerC_differentiable κ k).continuous.comp
    (Complex.continuous_ofReal.comp (continuous_norm : Continuous (fun x : Space => ‖x‖)))
  fin_cases j
  · exact hc.mul (coordinate 1).continuous
  · exact hc.neg.mul (coordinate 0).continuous
  · exact continuous_const

theorem centerE_differentiableAt (κ : ℂ) (x : Space) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => centerE κ y j) x := by
  by_cases hx : x = 0
  · subst x
    exact (centerE_hasFDerivAt_zero κ j).differentiableAt
  have hn := Complex.ofRealCLM.differentiableAt.comp x (differentiableAt_id.norm ℝ hx)
  have ha := ((centerA_differentiable κ (‖x‖ : ℂ)).restrictScalars ℝ).comp x hn
  have hb := ((centerB_differentiable κ (‖x‖ : ℂ)).restrictScalars ℝ).comp x hn
  fin_cases j
  · exact (hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 0)
  · exact (hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 1)
  · exact ha.add ((hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 2))

theorem centerH_differentiableAt (κ k : ℂ) (x : Space) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => centerH κ k y j) x := by
  by_cases hx : x = 0
  · subst x
    have hc : ContinuousAt (fun y : Space => centerC κ k (‖y‖ : ℂ)) 0 :=
      ((centerC_differentiable κ k).continuous.comp
        (Complex.continuous_ofReal.comp continuous_norm)).continuousAt
    fin_cases j
    · exact (continuous_mul_coordinate _ hc 1).differentiableAt
    · have h := (continuous_mul_coordinate _ hc 0).neg.differentiableAt
      simpa [centerH, swirlField, neg_mul] using h
    · exact differentiableAt_const _
  have hn := Complex.ofRealCLM.differentiableAt.comp x (differentiableAt_id.norm ℝ hx)
  have hc := ((centerC_differentiable κ k (‖x‖ : ℂ)).restrictScalars ℝ).comp x hn
  fin_cases j
  · exact hc.mul (coordinate_differentiableAt x 1)
  · exact hc.neg.mul (coordinate_differentiableAt x 0)
  · exact differentiableAt_const _

def entireInnerE (n k a : ℂ) : Field := fun x => (a/n) • centerE (n*k) x
def entireInnerH (n k a : ℂ) : Field := fun x => (a/n) • centerH (n*k) k x

theorem entireInnerE_eq (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) : entireInnerE n k a x = innerE n k a x := by
  simp only [entireInnerE, innerE, centerE_eq_regular _ (mul_ne_zero hn hk) x hx]

theorem entireInnerH_eq (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) : entireInnerH n k a x = innerH n k a x := by
  simp only [entireInnerH, innerH, centerH_eq_regular _ k (mul_ne_zero hn hk) x hx]

theorem entireInner_maxwell (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (x : Space) :
    ComplexMaxwellAt k (n^2) (entireInnerE n k a) (entireInnerH n k a) x :=
  complexMaxwell_scale k (n^2) (a/n) _ _ x
    (centerE_differentiableAt (n*k) x) (centerH_differentiableAt (n*k) k x)
    (center_maxwell (n*k) k (n^2) (mul_ne_zero hn hk) hk (by ring) x)

/-- Actual high-Q dipole transmission fields with no missing center point.
The global weak assembly across the spherical interface is separate. -/
theorem exists_high_quality_regular_transmission (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k a b : ℂ, k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ L < k.re ∧ k.im < 0 ∧
      Q < k.re / (-2*k.im) ∧
      (∀ x : Space, ‖x‖ = 1 →
        tangent x (entireInnerE (n : ℂ) k a x) = tangent x (outerE k b x) ∧
        tangent x (entireInnerH (n : ℂ) k a x) = tangent x (outerH k b x)) ∧
      (∀ x : Space, ComplexMaxwellAt k ((n : ℂ)^2)
        (entireInnerE (n : ℂ) k a) (entireInnerH (n : ℂ) k a) x) ∧
      (∀ x : Space, x ≠ 0 → ComplexMaxwellAt k 1 (outerE k b) (outerH k b) x) ∧
      ∃ x : Space, ‖x‖ = 1 ∧
        (tangent x (outerE k b x) ≠ 0 ∨ tangent x (outerH k b x) ≠ 0) := by
  obtain ⟨k,a,b,hk,ha,hb,hL,hi,hQ',hm,-,ho,hne⟩ :=
    exists_high_quality_transmission_fields n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  refine ⟨k,a,b,hk,ha,hb,hL,hi,hQ',?_,?_,ho,hne⟩
  · intro x hx
    have hx0 : x ≠ 0 := by intro h; simp [h] at hx
    rw [entireInnerE_eq _ _ _ hn0 hk x hx0, entireInnerH_eq _ _ _ hn0 hk x hx0]
    exact hm x hx
  · exact fun x => entireInner_maxwell (n : ℂ) k a hn0 hk x

end OQ14.ModalOrigin

#print axioms OQ14.ModalOrigin.expTail_series
#print axioms OQ14.ModalOrigin.expTail_zero
#print axioms OQ14.ModalOrigin.expTail_differentiable
#print axioms OQ14.ModalOrigin.expTail_step
#print axioms OQ14.ModalOrigin.profile_differentiable
#print axioms OQ14.ModalOrigin.profile_zero
#print axioms OQ14.ModalOrigin.profile_hasDerivAt_zero
#print axioms OQ14.ModalOrigin.expTail_two_identity
#print axioms OQ14.ModalOrigin.expTail_three_identity
#print axioms OQ14.ModalOrigin.psi_profile
#print axioms OQ14.ModalOrigin.psiD_profile
#print axioms OQ14.ModalOrigin.radial_zero_derivative
#print axioms OQ14.ModalOrigin.continuous_mul_coordinate
#print axioms OQ14.ModalOrigin.continuous_mul_two_coordinates
#print axioms OQ14.ModalOrigin.profile_deriv_differentiable
#print axioms OQ14.ModalOrigin.profileSlope_differentiable
#print axioms OQ14.ModalOrigin.profileSlope_identity
#print axioms OQ14.ModalOrigin.centerA_differentiable
#print axioms OQ14.ModalOrigin.centerB_differentiable
#print axioms OQ14.ModalOrigin.centerC_differentiable
#print axioms OQ14.ModalOrigin.centerA_zero
#print axioms OQ14.ModalOrigin.centerC_zero
#print axioms OQ14.ModalOrigin.centerA_hasDerivAt_zero
#print axioms OQ14.ModalOrigin.centerA_eq
#print axioms OQ14.ModalOrigin.centerB_eq
#print axioms OQ14.ModalOrigin.centerC_eq
#print axioms OQ14.ModalOrigin.centerE_eq_regular
#print axioms OQ14.ModalOrigin.centerH_eq_regular
#print axioms OQ14.ModalOrigin.centerE_hasFDerivAt_zero
#print axioms OQ14.ModalOrigin.centerE_zero
#print axioms OQ14.ModalOrigin.centerH_zero
#print axioms OQ14.ModalOrigin.centerE_curl_zero
#print axioms OQ14.ModalOrigin.centerH_curl_zero
#print axioms OQ14.ModalOrigin.center_maxwell_zero
#print axioms OQ14.ModalOrigin.curl_eventuallyEq
#print axioms OQ14.ModalOrigin.center_maxwell
#print axioms OQ14.ModalOrigin.centerE_continuous
#print axioms OQ14.ModalOrigin.centerH_continuous
#print axioms OQ14.ModalOrigin.centerE_differentiableAt
#print axioms OQ14.ModalOrigin.centerH_differentiableAt
#print axioms OQ14.ModalOrigin.entireInnerE_eq
#print axioms OQ14.ModalOrigin.entireInnerH_eq
#print axioms OQ14.ModalOrigin.entireInner_maxwell
#print axioms OQ14.ModalOrigin.exists_high_quality_regular_transmission

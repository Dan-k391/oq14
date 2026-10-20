import ModalInterface
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual complex-frequency outgoing asymptotics of the spherical dipole

The exponential is removed explicitly, as required at complex resonant
frequencies in the lower half plane. Exact ray formulas imply the outgoing
far-field limit and a uniform inverse-square weighted radiation defect.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalOutgoing

open Complex Filter OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalDipole OQ14.ModalInterface
open scoped Topology

def scaledElectric (k b : ℂ) (r : ℝ) (d : Space) : Vector :=
  (Complex.exp (-I*k*r)*(r : ℂ)) • outerE k b (r • d)

def scaledMagnetic (k b : ℂ) (r : ℝ) (d : Space) : Vector :=
  (Complex.exp (-I*k*r)*(r : ℂ)) • outerH k b (r • d)

def electricFar (k b : ℂ) (d : Space) : Vector :=
  ![b*I*k*(d 2 : ℂ)*(d 0 : ℂ),
    b*I*k*(d 2 : ℂ)*(d 1 : ℂ),
    b*(-I*k+I*k*(d 2 : ℂ)*(d 2 : ℂ))]

def magneticFar (k b : ℂ) (d : Space) : Vector :=
  ![-b*I*k*(d 1 : ℂ), b*I*k*(d 0 : ℂ), 0]

theorem exponential_cancel (z : ℂ) : Complex.exp (-I*z) * Complex.exp (I*z) = 1 := by
  rw [← Complex.exp_add]
  simp

theorem scaled_hankel (z : ℂ) :
    Complex.exp (-I*z)*xi 1 z = -(1+I/z) := by
  simp only [xi, p_one]
  norm_num
  calc
    _ = -(Complex.exp (-I*z)*Complex.exp (I*z))*(1+I/z) := by ring
    _ = _ := by rw [exponential_cancel]; ring

theorem scaled_hankelD (z : ℂ) :
    Complex.exp (-I*z)*xiD 1 z = -(I*(1+I/z)-I/z^2) := by
  simp only [xiD, p_one, pD_one]
  norm_num
  calc
    _ = -(Complex.exp (-I*z)*Complex.exp (I*z))*(I*(1+I/z)-I/z^2) := by ring
    _ = _ := by rw [exponential_cancel]; ring

theorem ray_norm (r : ℝ) (hr : 0 < r) (d : Space) (hd : ‖d‖ = 1) :
    ‖r • d‖ = r := by
  simp [norm_smul, hd, abs_of_pos hr]

theorem electric_ray_formula (k b : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : 0 < r) (d : Space) (hd : ‖d‖ = 1) :
    scaledElectric k b r d =
      ![b*(I*k-3/(r : ℂ)-3*I/(k*(r : ℂ)^2))*(d 2 : ℂ)*(d 0 : ℂ),
        b*(I*k-3/(r : ℂ)-3*I/(k*(r : ℂ)^2))*(d 2 : ℂ)*(d 1 : ℂ),
        b*((-I*k+1/(r : ℂ)+I/(k*(r : ℂ)^2))+
          (I*k-3/(r : ℂ)-3*I/(k*(r : ℂ)^2))*(d 2 : ℂ)*(d 2 : ℂ))] := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hr)
  have he : Complex.exp (-I*k*(r : ℂ)) = Complex.exp (-I*(k*(r : ℂ))) := by congr 1; ring
  have h1 := scaled_hankel (k*(r : ℂ))
  have h2 := scaled_hankelD (k*(r : ℂ))
  have hA : Complex.exp (-I*(k*(r : ℂ))) * (r : ℂ) *
      (k*xiD 1 (k*(r : ℂ))/(r : ℂ)) =
      -I*k+1/(r : ℂ)+I/(k*(r : ℂ)^2) := by
    calc
      _ = k*(Complex.exp (-I*(k*(r : ℂ)))*xiD 1 (k*(r : ℂ))) := by
        field_simp
        ring
      _ = _ := by
        rw [h2]
        field_simp [hk,hr0]
        ring_nf
        simp [I_sq]
  have hB : Complex.exp (-I*(k*(r : ℂ))) * (r : ℂ) *
      (2*xi 1 (k*(r : ℂ))/(r : ℂ)^4-k*xiD 1 (k*(r : ℂ))/(r : ℂ)^3) *
      (r : ℂ) * (r : ℂ) =
      I*k-3/(r : ℂ)-3*I/(k*(r : ℂ)^2) := by
    calc
      _ = (2/(r : ℂ))*(Complex.exp (-I*(k*(r : ℂ)))*xi 1 (k*(r : ℂ))) -
          k*(Complex.exp (-I*(k*(r : ℂ)))*xiD 1 (k*(r : ℂ))) := by
        field_simp
        ring
      _ = _ := by
        rw [h1,h2]
        field_simp [hk,hr0]
        ring_nf
        simp only [I_sq]
        ring
  simp only [neg_mul, mul_assoc] at hA hB
  ext j
  fin_cases j <;>
    simp [scaledElectric, outerE, outgoingE, dipoleE, axisField,
      electricA, electricB, scaledRadial, scaledRadialD, ray_norm r hr d hd,
      Pi.smul_apply, smul_eq_mul, PiLp.smul_apply, ofReal_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, he, mul_assoc]
  · linear_combination (b*(d 2 : ℂ)*(d 0 : ℂ)) * hB
  · linear_combination (b*(d 2 : ℂ)*(d 1 : ℂ)) * hB
  · linear_combination b * hA + (b*(d 2 : ℂ)*(d 2 : ℂ)) * hB

theorem magnetic_ray_formula (k b : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : 0 < r) (d : Space) (hd : ‖d‖ = 1) :
    scaledMagnetic k b r d =
      ![b*(-I*k+1/(r : ℂ))*(d 1 : ℂ),
        -b*(-I*k+1/(r : ℂ))*(d 0 : ℂ), 0] := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hr)
  have he : Complex.exp (-I*k*(r : ℂ)) = Complex.exp (-I*(k*(r : ℂ))) := by congr 1; ring
  have hC : Complex.exp (-I*(k*(r : ℂ))) * (r : ℂ) *
      ((I*k^2/k)*xi 1 (k*(r : ℂ))/(r : ℂ)^2) * (r : ℂ) =
      -I*k+1/(r : ℂ) := by
    calc
      _ = (I*k)*(Complex.exp (-I*(k*(r : ℂ)))*xi 1 (k*(r : ℂ))) := by
        field_simp
        ring
      _ = _ := by
        rw [scaled_hankel]
        field_simp
        ring_nf
        simp [I_sq]
  simp only [neg_mul, mul_assoc] at hC
  ext j
  fin_cases j <;>
    simp [scaledMagnetic, outerH, outgoingH, dipoleH, swirlField,
      magneticC, scaledRadial, ray_norm r hr d hd, Pi.smul_apply,
      smul_eq_mul, PiLp.smul_apply, ofReal_mul, he, mul_assoc]
  · linear_combination (b*(d 1 : ℂ)) * hC
  · linear_combination (b*(d 0 : ℂ)) * hC

def electricPolynomial (k b u : ℂ) (d : Space) : Vector :=
  ![b*(I*k-3*u-(3*I/k)*u^2)*(d 2 : ℂ)*(d 0 : ℂ),
    b*(I*k-3*u-(3*I/k)*u^2)*(d 2 : ℂ)*(d 1 : ℂ),
    b*((-I*k+u+(I/k)*u^2)+(I*k-3*u-(3*I/k)*u^2)*(d 2 : ℂ)*(d 2 : ℂ))]

def magneticPolynomial (k b u : ℂ) (d : Space) : Vector :=
  ![b*(-I*k+u)*(d 1 : ℂ), -b*(-I*k+u)*(d 0 : ℂ), 0]

theorem inverse_radius_tendsto :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using
    (continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))

theorem electric_far_limit (k b : ℂ) (hk : k ≠ 0)
    (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => scaledElectric k b r d) atTop (𝓝 (electricFar k b d)) := by
  have hp : Continuous (fun u : ℂ => electricPolynomial k b u d) := by
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [electricPolynomial] <;> fun_prop
  have ht := (hp.tendsto 0).comp inverse_radius_tendsto
  have hzero : electricPolynomial k b 0 d = electricFar k b d := by
    ext j
    fin_cases j <;> dsimp [electricPolynomial, electricFar] <;> ring
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [electric_ray_formula k b hk r hr d hd]
  ext j
  fin_cases j <;> dsimp [electricPolynomial, Function.comp_def] <;>
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring

theorem magnetic_far_limit (k b : ℂ) (hk : k ≠ 0)
    (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => scaledMagnetic k b r d) atTop (𝓝 (magneticFar k b d)) := by
  have hp : Continuous (fun u : ℂ => magneticPolynomial k b u d) := by
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [magneticPolynomial] <;> fun_prop
  have ht := (hp.tendsto 0).comp inverse_radius_tendsto
  have hzero : magneticPolynomial k b 0 d = magneticFar k b d := by
    ext j
    fin_cases j <;> dsimp [magneticPolynomial, magneticFar] <;> ring
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [magnetic_ray_formula k b hk r hr d hd]
  ext j
  fin_cases j <;> dsimp [magneticPolynomial, Function.comp_def] <;>
    simp only [div_eq_mul_inv] <;> ring

def radiationDefect (k b : ℂ) (r : ℝ) (d : Space) : Vector :=
  scaledMagnetic k b r d - tangent d (scaledElectric k b r d)

theorem radiationDefect_actual (k b : ℂ) (r : ℝ) (d : Space) :
    radiationDefect k b r d =
      (Complex.exp (-I*k*r)*(r : ℂ)) •
        (outerH k b (r • d) - tangent d (outerE k b (r • d))) := by
  rw [radiationDefect, scaledElectric, scaledMagnetic, tangent_smul, smul_sub]

theorem radiationDefect_formula (k b : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : 0 < r) (d : Space) (hd : ‖d‖ = 1) :
    radiationDefect k b r d =
      (-b*I/(k*(r : ℂ)^2)) • ![(d 1 : ℂ), -(d 0 : ℂ), 0] := by
  rw [radiationDefect, electric_ray_formula k b hk r hr d hd,
    magnetic_ray_formula k b hk r hr d hd]
  ext j
  fin_cases j <;> simp only [tangent, cross_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
    dsimp <;> ring

theorem radiationDefect_bound (k b : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : 0 < r) (d : Space) (hd : ‖d‖ = 1) :
    ‖radiationDefect k b r d‖ ≤ ‖b‖ / (‖k‖ * r^2) := by
  rw [radiationDefect_formula k b hk r hr d hd, norm_smul]
  have hnorm : ‖(![(d 1 : ℂ), -(d 0 : ℂ), 0] : Vector)‖ ≤ 1 := by
    apply pi_norm_le_iff_of_nonneg zero_le_one |>.mpr
    intro j
    fin_cases j
    · simpa [Complex.norm_real, hd] using PiLp.norm_apply_le d 1
    · simpa [Complex.norm_real, hd] using PiLp.norm_apply_le d 0
    · simp
  calc
    _ ≤ ‖-b*I/(k*(r : ℂ)^2)‖ * 1 :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := by simp [norm_div, norm_mul, norm_pow, abs_of_pos hr]

theorem radiationDefect_limit (k b : ℂ) (hk : k ≠ 0)
    (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => radiationDefect k b r d) atTop (𝓝 0) := by
  have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => -b*I/k) atTop
    (𝓝 (-b*I/k))).mul (inverse_radius_tendsto.pow 2)).smul
      (tendsto_const_nhds (x := (![(d 1 : ℂ), -(d 0 : ℂ), 0] : Vector))))
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_smul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [radiationDefect_formula k b hk r hr d hd]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem radiationDefect_varying_direction (k b : ℂ) (hk : k ≠ 0)
    (d : ℝ → Space) (hd : ∀ᶠ r in atTop, ‖d r‖ = 1) :
    Tendsto (fun r : ℝ => radiationDefect k b r (d r)) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => (‖b‖/‖k‖) * (r⁻¹)^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).pow 2))
  apply squeeze_zero_norm' _ ht
  filter_upwards [hd, eventually_gt_atTop (0 : ℝ)] with r hdr hr
  convert radiationDefect_bound k b hk r hr (d r) hdr using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem far_tangential_relation (k b : ℂ) (d : Space) :
    tangent d (electricFar k b d) = magneticFar k b d := by
  ext j
  fin_cases j <;> simp only [tangent, cross_apply, electricFar, magneticFar] <;>
    dsimp <;> ring

theorem far_field_nonzero (k b : ℂ) (hk : k ≠ 0) (hb : b ≠ 0) :
    ∃ d : Space, ‖d‖ = 1 ∧ electricFar k b d ≠ 0 ∧ magneticFar k b d ≠ 0 := by
  let d : Space := EuclideanSpace.single 0 1
  refine ⟨d, by simp [d], ?_, ?_⟩
  · intro h
    have he := congrFun h (2 : Fin 3)
    simp [electricFar, d, hk, hb, I_ne_zero] at he
  · intro h
    have he := congrFun h (1 : Fin 3)
    simp [magneticFar, d, hk, hb, I_ne_zero] at he

def unitDirection (x : Space) : Space := ‖x‖⁻¹ • x

theorem unitDirection_norm (x : Space) (hx : x ≠ 0) : ‖unitDirection x‖ = 1 := by
  simp only [unitDirection, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem radius_unitDirection (x : Space) (hx : x ≠ 0) :
    ‖x‖ • unitDirection x = x := by
  rw [unitDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem tangent_unitDirection (x : Space) (v : Vector) :
    tangent (unitDirection x) v = ((‖x‖ : ℂ)⁻¹) • tangent x v := by
  ext j
  fin_cases j <;>
    simp [tangent, cross_apply, unitDirection, PiLp.smul_apply, ofReal_mul, ofReal_inv] <;> ring

def spatialRadiationDefect (k b : ℂ) (x : Space) : Vector :=
  (Complex.exp (-I*k*‖x‖)*(‖x‖ : ℂ)) •
    (outerH k b x - ((‖x‖ : ℂ)⁻¹) • tangent x (outerE k b x))

theorem spatialRadiationDefect_eq (k b : ℂ) (x : Space) (hx : x ≠ 0) :
    spatialRadiationDefect k b x =
      radiationDefect k b ‖x‖ (unitDirection x) := by
  rw [radiationDefect_actual, radius_unitDirection x hx, tangent_unitDirection]
  rfl

theorem spatialRadiationDefect_bound (k b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) :
    ‖spatialRadiationDefect k b x‖ ≤ ‖b‖ / (‖k‖ * ‖x‖^2) := by
  rw [spatialRadiationDefect_eq k b x hx]
  exact radiationDefect_bound k b hk ‖x‖ (norm_pos_iff.mpr hx)
    (unitDirection x) (unitDirection_norm x hx)

/-- The exponentially weighted outgoing condition holds along every path
whose radius tends to infinity, including varying angular direction. -/
theorem spatialRadiationDefect_limit (k b : ℂ) (hk : k ≠ 0)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => spatialRadiationDefect k b (γ t)) atTop (𝓝 0) := by
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hγ
  have ht : Tendsto (fun t : ℝ => (‖b‖/‖k‖) * (‖γ t‖⁻¹)^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hi.pow 2))
  apply squeeze_zero_norm' _ ht
  filter_upwards [hγ.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hx : γ t ≠ 0 := norm_pos_iff.mp ht
  convert spatialRadiationDefect_bound k b hk (γ t) hx using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

end OQ14.ModalOutgoing


#print axioms OQ14.ModalOutgoing.exponential_cancel
#print axioms OQ14.ModalOutgoing.scaled_hankel
#print axioms OQ14.ModalOutgoing.scaled_hankelD
#print axioms OQ14.ModalOutgoing.ray_norm
#print axioms OQ14.ModalOutgoing.electric_ray_formula
#print axioms OQ14.ModalOutgoing.magnetic_ray_formula
#print axioms OQ14.ModalOutgoing.inverse_radius_tendsto
#print axioms OQ14.ModalOutgoing.electric_far_limit
#print axioms OQ14.ModalOutgoing.magnetic_far_limit
#print axioms OQ14.ModalOutgoing.radiationDefect_actual
#print axioms OQ14.ModalOutgoing.radiationDefect_formula
#print axioms OQ14.ModalOutgoing.radiationDefect_bound
#print axioms OQ14.ModalOutgoing.radiationDefect_limit
#print axioms OQ14.ModalOutgoing.radiationDefect_varying_direction
#print axioms OQ14.ModalOutgoing.far_tangential_relation
#print axioms OQ14.ModalOutgoing.far_field_nonzero
#print axioms OQ14.ModalOutgoing.unitDirection_norm
#print axioms OQ14.ModalOutgoing.radius_unitDirection
#print axioms OQ14.ModalOutgoing.tangent_unitDirection
#print axioms OQ14.ModalOutgoing.spatialRadiationDefect_eq
#print axioms OQ14.ModalOutgoing.spatialRadiationDefect_bound
#print axioms OQ14.ModalOutgoing.spatialRadiationDefect_limit

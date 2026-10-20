import ModalWronskian
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Actual radial Riccati basis for the Rellich argument

Variation coefficients are differentiated from the scalar differential
equation and proved independent of radius on a connected half-line. The actual
finite Riccati--Hankel functions supply the nonzero Wronskian basis.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialRellich

open Complex Filter Set OQ14.ModalAlgebra OQ14.ModalWronskian
open scoped Topology

theorem ode_wronskian_hasDerivAt (f df u du q : ℝ → ℂ) (r : ℝ)
    (hf : HasDerivAt f (df r) r) (hdf : HasDerivAt df (q r*f r) r)
    (hu : HasDerivAt u (du r) r) (hdu : HasDerivAt du (q r*u r) r) :
    HasDerivAt (fun t => f t*du t-u t*df t) 0 r := by
  convert (hf.mul hdu).sub (hu.mul hdf) using 1
  ring

theorem ode_two_solution_expansion (R : ℝ) (f df u du v dv q : ℝ → ℂ) (W : ℂ)
    (hW : W ≠ 0)
    (hf : ∀ r, R < r → HasDerivAt f (df r) r)
    (hdf : ∀ r, R < r → HasDerivAt df (q r*f r) r)
    (hu : ∀ r, R < r → HasDerivAt u (du r) r)
    (hdu : ∀ r, R < r → HasDerivAt du (q r*u r) r)
    (hv : ∀ r, R < r → HasDerivAt v (dv r) r)
    (hdv : ∀ r, R < r → HasDerivAt dv (q r*v r) r)
    (hwr : ∀ r, R < r → u r*dv r-v r*du r = W) :
    ∃ a b : ℂ, ∀ r, R < r → f r = a*u r+b*v r := by
  let ac : ℝ → ℂ := fun r => (f r*dv r-v r*df r)/W
  let bc : ℝ → ℂ := fun r => (u r*df r-f r*du r)/W
  have ha (r : ℝ) (hr : R < r) : HasDerivAt ac 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt f df v dv q r (hf r hr) (hdf r hr) (hv r hr) (hdv r hr)).div_const W
  have hb (r : ℝ) (hr : R < r) : HasDerivAt bc 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt u du f df q r (hu r hr) (hdu r hr) (hf r hr) (hdf r hr)).div_const W
  obtain ⟨a,hae⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero (convex_Ioi R).isPreconnected
    (fun r hr => (ha r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (ha r hr).deriv)
  obtain ⟨b,hbe⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero (convex_Ioi R).isPreconnected
    (fun r hr => (hb r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hb r hr).deriv)
  refine ⟨a,b,?_⟩
  intro r hr
  rw [← hae r hr, ← hbe r hr]
  dsimp only [ac,bc]
  field_simp [hW]
  linear_combination -f r*(hwr r hr)

def outgoing (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := xi l (k*r)
def outgoingD (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := k*xiD l (k*r)
def incoming (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := xiMinus l (k*r)
def incomingD (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := k*xiMinusD l (k*r)
def radialCoefficient (l : ℕ) (k : ℂ) (r : ℝ) : ℂ :=
  (l : ℂ)*(l+1)/(r : ℂ)^2-k^2

theorem outgoing_hasDerivAt (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : r ≠ 0) : HasDerivAt (outgoing l k) (outgoingD l k r) r := by
  have h := ((xi_hasDerivAt l (k*r) (mul_ne_zero hk (ofReal_ne_zero.mpr hr))).comp
    (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul k)).comp_ofReal
  convert h using 1
  dsimp [outgoingD]
  ring

theorem incoming_hasDerivAt (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : r ≠ 0) : HasDerivAt (incoming l k) (incomingD l k r) r := by
  have h := ((xiMinus_hasDerivAt l (k*r) (mul_ne_zero hk (ofReal_ne_zero.mpr hr))).comp
    (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul k)).comp_ofReal
  convert h using 1
  dsimp [incomingD]
  ring

theorem curvature_scale (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    k^2*((l : ℂ)*(l+1)/(k*r)^2-1) = radialCoefficient l k r := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  unfold radialCoefficient
  field_simp
  ring

theorem outgoingD_hasDerivAt (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (outgoingD l k) (radialCoefficient l k r*outgoing l k r) r := by
  have h := (((xiD_hasDerivAt l (k*r) (mul_ne_zero hk (ofReal_ne_zero.mpr hr))).comp
    (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul k)).const_mul k).comp_ofReal
  convert h using 1
  dsimp only [outgoing]
  rw [← curvature_scale l k hk r hr]
  ring

theorem incomingD_hasDerivAt (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (incomingD l k) (radialCoefficient l k r*incoming l k r) r := by
  have h := (((xiMinusD_hasDerivAt l (k*r) (mul_ne_zero hk (ofReal_ne_zero.mpr hr))).comp
    (r : ℂ) ((hasDerivAt_id (r : ℂ)).const_mul k)).const_mul k).comp_ofReal
  convert h using 1
  dsimp only [incoming]
  rw [← curvature_scale l k hk r hr]
  ring

theorem radial_wronskian (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    outgoing l k r*incomingD l k r-incoming l k r*outgoingD l k r = -2*I*k := by
  have h := hankel_wronskian l (k*r) (mul_ne_zero hk (ofReal_ne_zero.mpr hr))
  dsimp [outgoing,outgoingD,incoming,incomingD]
  linear_combination k*h

theorem radial_ode_expansion (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r, R < r → HasDerivAt f (df r) r)
    (hdf : ∀ r, R < r → HasDerivAt df (radialCoefficient l k r*f r) r) :
    ∃ a b : ℂ, ∀ r, R < r → f r = a*outgoing l k r+b*incoming l k r := by
  have hW : -2*I*k ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hk
  exact ode_two_solution_expansion R f df _ _ _ _ _ _ hW hf hdf
    (fun r hr => outgoing_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr)))
    (fun r hr => outgoingD_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr)))
    (fun r hr => incoming_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr)))
    (fun r hr => incomingD_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr)))
    (fun r hr => radial_wronskian l k hk r (ne_of_gt (lt_of_le_of_lt hR hr)))

def phase (k r : ℝ) : ℂ := Complex.exp (-I*(k : ℂ)*(r : ℂ))

theorem phase_norm (k r : ℝ) : ‖phase k r‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem phase_mul_zero_limit (k : ℝ) (f : ℝ → ℂ)
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun r => phase k r*f r) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa only [norm_zero] using hf.norm)
  filter_upwards with r
  simp only [norm_mul,phase_norm,one_mul]
  exact le_rfl

theorem hankelPoly_radial_limit (l : ℕ) (k : ℂ) (_hk : k ≠ 0) (s : ℂ) :
    Tendsto (fun r : ℝ => hankelPoly l s (k*r)) atTop (𝓝 1) := by
  have hi : Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
        (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have hik : Tendsto (fun r : ℝ => (k*(r : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa only [mul_inv_rev, zero_mul] using hi.mul_const k⁻¹
  have hp := (inversePoly_hasDerivAt l s 0).continuousAt.tendsto.comp hik
  rw [inversePoly_zero] at hp
  simpa only [Function.comp_def,inversePoly_eq,inv_inv] using hp

theorem outgoing_scaled_formula (l : ℕ) (k r : ℝ) :
    phase k r*outgoing l (k : ℂ) r = (-I)^(l+1)*p l ((k : ℂ)*r) := by
  unfold phase outgoing xi
  calc
    _ = (-I)^(l+1)*(Complex.exp (-I*(k : ℂ)*r)*Complex.exp (I*((k : ℂ)*r)))*
        p l ((k : ℂ)*r) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp only [neg_mul,mul_assoc,neg_add_cancel,Complex.exp_zero];ring

theorem incoming_scaled_formula (l : ℕ) (k r : ℝ) :
    phase k r*incoming l (k : ℂ) r = I^(l+1)*phase (2*k) r*pMinus l ((k : ℂ)*r) := by
  unfold phase incoming xiMinus
  have he : Complex.exp (-I*(k : ℂ)*r)*Complex.exp (-I*((k : ℂ)*r)) =
      Complex.exp (-I*((2*k : ℝ) : ℂ)*r) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (I^(l+1)*pMinus l ((k : ℂ)*r))*he

theorem outgoing_scaled_limit (l : ℕ) (k : ℝ) (hk : 0 < k) :
    Tendsto (fun r => phase k r*outgoing l (k : ℂ) r) atTop (𝓝 ((-I)^(l+1))) := by
  simp_rw [outgoing_scaled_formula]
  simpa only [mul_one] using (hankelPoly_radial_limit l (k : ℂ)
    (ofReal_ne_zero.mpr hk.ne') I).const_mul ((-I)^(l+1))

theorem incoming_scaled_error_limit (l : ℕ) (k : ℝ) (hk : 0 < k) :
    Tendsto (fun r => phase k r*incoming l (k : ℂ) r-I^(l+1)*phase (2*k) r)
      atTop (𝓝 0) := by
  have ht := phase_mul_zero_limit (2*k) _
    (by simpa only [sub_self,mul_zero] using
      (((hankelPoly_radial_limit l (k : ℂ) (ofReal_ne_zero.mpr hk.ne') (-I)).sub_const 1).const_mul
        (I^(l+1))))
  convert ht using 1
  funext r
  rw [incoming_scaled_formula]
  dsimp [pMinus]
  ring

theorem phase_half_period (k : ℝ) (hk : 0 < k) (r : ℝ) :
    phase (2*k) (r+Real.pi/(2*k)) = -phase (2*k) r := by
  unfold phase
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have he : -I*((2*k : ℝ) : ℂ)*(r+Real.pi/(2*k) : ℝ) =
      -I*((2*k : ℝ) : ℂ)*(r : ℂ) + -(Real.pi : ℂ)*I := by
    push_cast
    field_simp [hk0]
    ring
  rw [he,Complex.exp_add]
  have hp : Complex.exp (-(Real.pi : ℂ)*I) = -1 := by
    rw [neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  rw [hp,mul_neg_one]

theorem oscillatory_zero_limit (k : ℝ) (hk : 0 < k) (a b : ℂ)
    (h : Tendsto (fun r => a+b*phase (2*k) r) atTop (𝓝 0)) : a = 0 ∧ b = 0 := by
  have hshift : Tendsto (fun r : ℝ => r+Real.pi/(2*k)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hsum := h.add (h.comp hshift)
  have ht : Tendsto (fun _ : ℝ => 2*a) atTop (𝓝 0) := by
    convert hsum using 1
    · funext r
      dsimp only [Function.comp_def]
      rw [phase_half_period k hk]
      ring
    · simp
  have ha : a = 0 := by
    have he := tendsto_nhds_unique ht tendsto_const_nhds
    linear_combination -he/2
  have hn := h.norm
  simp only [ha,zero_add,norm_mul,phase_norm,mul_one,norm_zero] at hn
  have hb : b = 0 := norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hn)
  exact ⟨ha,hb⟩

theorem hankel_combination_zero_limit (l : ℕ) (k : ℝ) (hk : 0 < k) (a b : ℂ)
    (h : Tendsto (fun r => a*outgoing l (k : ℂ) r+b*incoming l (k : ℂ) r)
      atTop (𝓝 0)) : a = 0 ∧ b = 0 := by
  have hscaled := phase_mul_zero_limit k _ h
  have ho : Tendsto (fun r => phase k r*outgoing l (k : ℂ) r-(-I)^(l+1)) atTop (𝓝 0) := by
    simpa only [sub_self] using (outgoing_scaled_limit l k hk).sub_const ((-I)^(l+1))
  have herr := (ho.const_mul a).add ((incoming_scaled_error_limit l k hk).const_mul b)
  have ht := hscaled.sub herr
  simp only [mul_zero,zero_add,sub_zero] at ht
  have hlead : Tendsto (fun r => a*(-I)^(l+1)+(b*I^(l+1))*phase (2*k) r) atTop (𝓝 0) := by
    convert ht using 1
    funext r
    ring
  obtain ⟨ha,hb⟩ := oscillatory_zero_limit k hk _ _ hlead
  exact ⟨(mul_eq_zero.mp ha).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)),
    (mul_eq_zero.mp hb).resolve_right (pow_ne_zero _ I_ne_zero)⟩

/-- A genuine solution of the fixed-degree radial Helmholtz equation on
the exterior half-line cannot have its Riccati amplitude tend to zero.
Its Hankel expansion is a conclusion of the actual derivative equations. -/
theorem radial_ode_zero_of_tendsto (l : ℕ) (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r, R < r → HasDerivAt f (df r) r)
    (hdf : ∀ r, R < r → HasDerivAt df (radialCoefficient l (k : ℂ) r*f r) r)
    (hlimit : Tendsto f atTop (𝓝 0)) : ∀ r, R < r → f r = 0 := by
  obtain ⟨a,b,hexp⟩ := radial_ode_expansion l (k : ℂ) (ofReal_ne_zero.mpr hk.ne') R hR f df hf hdf
  have hc : Tendsto (fun r => a*outgoing l (k : ℂ) r+b*incoming l (k : ℂ) r) atTop (𝓝 0) := by
    apply hlimit.congr'
    filter_upwards [eventually_gt_atTop R] with r hr
    exact hexp r hr
  obtain ⟨ha,hb⟩ := hankel_combination_zero_limit l k hk a b hc
  intro r hr
  rw [hexp r hr,ha,hb]
  simp

end OQ14.RadialRellich

#print axioms OQ14.RadialRellich.ode_wronskian_hasDerivAt
#print axioms OQ14.RadialRellich.ode_two_solution_expansion
#print axioms OQ14.RadialRellich.outgoing_hasDerivAt
#print axioms OQ14.RadialRellich.incoming_hasDerivAt
#print axioms OQ14.RadialRellich.curvature_scale
#print axioms OQ14.RadialRellich.outgoingD_hasDerivAt
#print axioms OQ14.RadialRellich.incomingD_hasDerivAt
#print axioms OQ14.RadialRellich.radial_wronskian
#print axioms OQ14.RadialRellich.radial_ode_expansion
#print axioms OQ14.RadialRellich.phase_norm
#print axioms OQ14.RadialRellich.phase_mul_zero_limit
#print axioms OQ14.RadialRellich.hankelPoly_radial_limit
#print axioms OQ14.RadialRellich.outgoing_scaled_formula
#print axioms OQ14.RadialRellich.incoming_scaled_formula
#print axioms OQ14.RadialRellich.outgoing_scaled_limit
#print axioms OQ14.RadialRellich.incoming_scaled_error_limit
#print axioms OQ14.RadialRellich.phase_half_period
#print axioms OQ14.RadialRellich.oscillatory_zero_limit
#print axioms OQ14.RadialRellich.hankel_combination_zero_limit
#print axioms OQ14.RadialRellich.radial_ode_zero_of_tendsto

import RadialRellich

/-! Actual radial basis selection from derivatives and a scaled outgoing limit. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.RadialBoundarySelection

open Complex Filter Set OQ14.RadialRellich
open scoped Topology

theorem hankel_scaled_limit (l : ℕ) (k : ℝ) (hk : 0 < k) (a b A : ℂ)
    (h : Tendsto (fun r => phase k r*(a*outgoing l (k : ℂ) r+b*incoming l (k : ℂ) r))
      atTop (𝓝 A)) : a*(-I)^(l+1)=A ∧ b=0 := by
  have ho : Tendsto (fun r => phase k r*outgoing l (k : ℂ) r-(-I)^(l+1)) atTop (𝓝 0) := by
    simpa only [sub_self] using (outgoing_scaled_limit l k hk).sub_const ((-I)^(l+1))
  have herr := (ho.const_mul a).add ((incoming_scaled_error_limit l k hk).const_mul b)
  have ht := (h.sub_const A).sub herr
  simp only [sub_self,mul_zero,zero_add,sub_zero] at ht
  have hlead : Tendsto (fun r => (a*(-I)^(l+1)-A)+(b*I^(l+1))*phase (2*k) r)
      atTop (𝓝 0) := by
    convert ht using 1
    funext r
    ring
  obtain ⟨ha,hb⟩ := oscillatory_zero_limit k hk _ _ hlead
  exact ⟨sub_eq_zero.mp ha,(mul_eq_zero.mp hb).resolve_right (pow_ne_zero _ I_ne_zero)⟩

theorem ode_outgoing_selection (l : ℕ) (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r, R < r → HasDerivAt f (df r) r)
    (hdf : ∀ r, R < r → HasDerivAt df (radialCoefficient l (k : ℂ) r*f r) r)
    (A : ℂ) (hA : Tendsto (fun r => phase k r*f r) atTop (𝓝 A)) :
    ∃ a : ℂ,(∀ r,R < r → f r=a*outgoing l (k : ℂ) r) ∧ A=a*(-I)^(l+1) := by
  obtain ⟨a,b,hexp⟩ := radial_ode_expansion l (k : ℂ) (ofReal_ne_zero.mpr hk.ne') R hR f df hf hdf
  have hc : Tendsto (fun r => phase k r*(a*outgoing l (k : ℂ) r+b*incoming l (k : ℂ) r))
      atTop (𝓝 A) := by
    apply hA.congr'
    filter_upwards [eventually_gt_atTop R] with r hr
    rw [hexp r hr]
  obtain ⟨ha,hb⟩ := hankel_scaled_limit l k hk a b A hc
  refine ⟨a,?_,ha.symm⟩
  intro r hr
  simpa only [hb,zero_mul,add_zero] using hexp r hr

theorem ode_two_solution_expansion_on (Ω : Set ℝ) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (f df u du v dv q : ℝ → ℂ) (W : ℂ) (hW : W ≠ 0)
    (hf : ∀ r ∈ Ω, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ω, HasDerivAt df (q r*f r) r)
    (hu : ∀ r ∈ Ω, HasDerivAt u (du r) r)
    (hdu : ∀ r ∈ Ω, HasDerivAt du (q r*u r) r)
    (hv : ∀ r ∈ Ω, HasDerivAt v (dv r) r)
    (hdv : ∀ r ∈ Ω, HasDerivAt dv (q r*v r) r)
    (hwr : ∀ r ∈ Ω,u r*dv r-v r*du r=W) :
    ∃ a b : ℂ,∀ r ∈ Ω,f r=a*u r+b*v r := by
  let ac : ℝ → ℂ := fun r => (f r*dv r-v r*df r)/W
  let bc : ℝ → ℂ := fun r => (u r*df r-f r*du r)/W
  have ha (r : ℝ) (hr : r ∈ Ω) : HasDerivAt ac 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt f df v dv q r (hf r hr) (hdf r hr) (hv r hr) (hdv r hr)).div_const W
  have hb (r : ℝ) (hr : r ∈ Ω) : HasDerivAt bc 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt u du f df q r (hu r hr) (hdu r hr) (hf r hr) (hdf r hr)).div_const W
  obtain ⟨a,hae⟩ := hΩ.exists_is_const_of_deriv_eq_zero hconn
    (fun r hr => (ha r hr).differentiableAt.differentiableWithinAt) (fun r hr => (ha r hr).deriv)
  obtain ⟨b,hbe⟩ := hΩ.exists_is_const_of_deriv_eq_zero hconn
    (fun r hr => (hb r hr).differentiableAt.differentiableWithinAt) (fun r hr => (hb r hr).deriv)
  refine ⟨a,b,?_⟩
  intro r hr
  rw [← hae r hr,← hbe r hr]
  dsimp only [ac,bc]
  field_simp [hW]
  linear_combination -f r*(hwr r hr)

theorem radial_ode_expansion_interval (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo R L,HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L,HasDerivAt df (radialCoefficient l k r*f r) r) :
    ∃ a b : ℂ,∀ r ∈ Ioo R L,f r=a*outgoing l k r+b*incoming l k r := by
  have hW : -2*I*k ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hk
  have hn (r : ℝ) (hr : r ∈ Ioo R L) : r ≠ 0 := ne_of_gt (lt_of_le_of_lt hR hr.1)
  exact ode_two_solution_expansion_on (Ioo R L) isOpen_Ioo (convex_Ioo R L).isPreconnected
    f df _ _ _ _ _ _ hW hf hdf
    (fun r hr => outgoing_hasDerivAt l k hk r (hn r hr))
    (fun r hr => outgoingD_hasDerivAt l k hk r (hn r hr))
    (fun r hr => incoming_hasDerivAt l k hk r (hn r hr))
    (fun r hr => incomingD_hasDerivAt l k hk r (hn r hr))
    (fun r hr => radial_wronskian l k hk r (hn r hr))

end OQ14.RadialBoundarySelection

#print axioms OQ14.RadialBoundarySelection.hankel_scaled_limit
#print axioms OQ14.RadialBoundarySelection.ode_outgoing_selection
#print axioms OQ14.RadialBoundarySelection.ode_two_solution_expansion_on
#print axioms OQ14.RadialBoundarySelection.radial_ode_expansion_interval

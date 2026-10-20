import RadialRellich

/-! # Actual finite-interval radial ODE uniqueness -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialIntervalUniqueness

open Complex Filter Set OQ14.RadialRellich
open scoped Topology

theorem wronskian_zero_on (Ω : Set ℝ) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (f df u du q : ℝ → ℂ)
    (hf : ∀ r ∈ Ω, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ω, HasDerivAt df (q r*f r) r)
    (hu : ∀ r ∈ Ω, HasDerivAt u (du r) r)
    (hdu : ∀ r ∈ Ω, HasDerivAt du (q r*u r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ω) (h₀ : f r₀ = 0) (hd₀ : df r₀ = 0) :
    ∀ r ∈ Ω, f r*du r-u r*df r = 0 := by
  have hd (r : ℝ) (hr : r ∈ Ω) :
      HasDerivAt (fun t => f t*du t-u t*df t) 0 r :=
    ode_wronskian_hasDerivAt f df u du q r (hf r hr) (hdf r hr) (hu r hr) (hdu r hr)
  obtain ⟨c,hc⟩ := hΩ.exists_is_const_of_deriv_eq_zero hconn
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv)
  have hc₀ : c = 0 := by simpa [h₀,hd₀] using (hc r₀ hr₀).symm
  intro r hr
  exact (hc r hr).trans hc₀

theorem ode_zero_on_of_basis (Ω : Set ℝ) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (f df u du v dv q : ℝ → ℂ)
    (hf : ∀ r ∈ Ω, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ω, HasDerivAt df (q r*f r) r)
    (hu : ∀ r ∈ Ω, HasDerivAt u (du r) r)
    (hdu : ∀ r ∈ Ω, HasDerivAt du (q r*u r) r)
    (hv : ∀ r ∈ Ω, HasDerivAt v (dv r) r)
    (hdv : ∀ r ∈ Ω, HasDerivAt dv (q r*v r) r)
    (hW : ∀ r ∈ Ω, u r*dv r-v r*du r ≠ 0)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ω) (h₀ : f r₀ = 0) (hd₀ : df r₀ = 0) :
    ∀ r ∈ Ω, f r = 0 ∧ df r = 0 := by
  have hfu := wronskian_zero_on Ω hΩ hconn f df u du q hf hdf hu hdu r₀ hr₀ h₀ hd₀
  have hfv := wronskian_zero_on Ω hΩ hconn f df v dv q hf hdf hv hdv r₀ hr₀ h₀ hd₀
  intro r hr
  have ha : f r*(u r*dv r-v r*du r) = 0 := by
    linear_combination u r*(hfv r hr)-v r*(hfu r hr)
  have hb : df r*(u r*dv r-v r*du r) = 0 := by
    linear_combination du r*(hfv r hr)-dv r*(hfu r hr)
  exact ⟨(mul_eq_zero.mp ha).resolve_right (hW r hr),
    (mul_eq_zero.mp hb).resolve_right (hW r hr)⟩

theorem radial_ode_zero_on_interval (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo R L, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L, HasDerivAt df (radialCoefficient l k r*f r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (h₀ : f r₀ = 0) (hd₀ : df r₀ = 0) :
    ∀ r ∈ Ioo R L, f r = 0 ∧ df r = 0 := by
  have hn (r : ℝ) (hr : r ∈ Ioo R L) : r ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt hR hr.1)
  apply ode_zero_on_of_basis (Ioo R L) isOpen_Ioo (convex_Ioo R L).isPreconnected
    f df (outgoing l k) (outgoingD l k) (incoming l k) (incomingD l k)
    (radialCoefficient l k) hf hdf
    (fun r hr => outgoing_hasDerivAt l k hk r (hn r hr))
    (fun r hr => outgoingD_hasDerivAt l k hk r (hn r hr))
    (fun r hr => incoming_hasDerivAt l k hk r (hn r hr))
    (fun r hr => incomingD_hasDerivAt l k hk r (hn r hr)) _ r₀ hr₀ h₀ hd₀
  intro r hr
  rw [radial_wronskian l k hk r (hn r hr)]
  exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hk

theorem radial_solutions_unique_on_interval (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (f df g dg : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo R L, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L, HasDerivAt df (radialCoefficient l k r*f r) r)
    (hg : ∀ r ∈ Ioo R L, HasDerivAt g (dg r) r)
    (hdg : ∀ r ∈ Ioo R L, HasDerivAt dg (radialCoefficient l k r*g r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (h₀ : f r₀ = g r₀) (hd₀ : df r₀ = dg r₀) :
    ∀ r ∈ Ioo R L, f r = g r ∧ df r = dg r := by
  have hz := radial_ode_zero_on_interval l k hk R L hR
    (fun r => f r-g r) (fun r => df r-dg r)
    (fun r hr => (hf r hr).sub (hg r hr))
    (fun r hr => by simpa only [mul_sub] using (hdf r hr).sub (hdg r hr))
    r₀ hr₀ (sub_eq_zero.mpr h₀) (sub_eq_zero.mpr hd₀)
  intro r hr
  exact ⟨sub_eq_zero.mp (hz r hr).1,sub_eq_zero.mp (hz r hr).2⟩

theorem radial_ode_zero_of_zero_neighborhood (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo R L, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L, HasDerivAt df (radialCoefficient l k r*f r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (hzero : f =ᶠ[𝓝 r₀] 0) :
    ∀ r ∈ Ioo R L, f r = 0 ∧ df r = 0 := by
  have h₀ : f r₀ = 0 := hzero.eq_of_nhds
  have hd₀ : df r₀ = 0 := by
    simpa only [(hf r₀ hr₀).deriv, deriv_zero] using hzero.deriv_eq
  exact radial_ode_zero_on_interval l k hk R L hR f df hf hdf r₀ hr₀ h₀ hd₀

end OQ14.RadialIntervalUniqueness

#print axioms OQ14.RadialIntervalUniqueness.wronskian_zero_on
#print axioms OQ14.RadialIntervalUniqueness.ode_zero_on_of_basis
#print axioms OQ14.RadialIntervalUniqueness.radial_ode_zero_on_interval
#print axioms OQ14.RadialIntervalUniqueness.radial_solutions_unique_on_interval
#print axioms OQ14.RadialIntervalUniqueness.radial_ode_zero_of_zero_neighborhood

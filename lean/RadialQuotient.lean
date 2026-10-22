import LocalRadialHarmonic

/-! Exact radial quotient derivatives converting a Riccati equation to the
scalar spherical Helmholtz equation. All derivatives are actual real derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RadialQuotient
open Set Filter OQ14.Maxwell OQ14.GreenKernel
open scoped Topology

def profile (l : ℕ) (u : ℝ → ℂ) (r : ℝ) : ℂ := u r/(r : ℂ)^(l+1)
def profileD (l : ℕ) (u uD : ℝ → ℂ) (r : ℝ) : ℂ :=
  uD r/(r : ℂ)^(l+1)-(l+1 : ℕ)*u r/(r : ℂ)^(l+2)
def profileDD (l : ℕ) (u uD : ℝ → ℂ) (w : ℂ) (r : ℝ) : ℂ :=
  w/(r : ℂ)^(l+1)-2*(l+1 : ℕ)*uD r/(r : ℂ)^(l+2)+
    (l+1 : ℕ)*(l+2 : ℕ)*u r/(r : ℂ)^(l+3)

theorem profile_hasDerivAt (l : ℕ) (u uD : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hu : HasDerivAt u (uD r) r) : HasDerivAt (profile l u) (profileD l u uD r) r := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hp : HasDerivAt (fun t : ℝ => (t : ℂ)^(l+1))
      ((l+1 : ℕ)*(r : ℂ)^l) r := by
    simpa only [Function.comp_def,smul_eq_mul,mul_one,one_mul,Nat.add_sub_cancel] using
      (hasDerivAt_pow (l+1) (r : ℂ)).scomp r (complex_radius_hasDerivAt r)
  convert hu.div hp (pow_ne_zero _ hrc) using 1
  simp only [profileD,Nat.add_sub_cancel,mul_one,pow_succ]
  field_simp [hrc,pow_ne_zero]
  ring

theorem profileD_hasDerivAt (l : ℕ) (u uD : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (w : ℂ) (hu : HasDerivAt u (uD r) r) (hud : HasDerivAt uD w r) :
    HasDerivAt (profileD l u uD) (profileDD l u uD w r) r := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have h1 := profile_hasDerivAt l uD (fun _ => w) r hr hud
  have h2 := (profile_hasDerivAt (l+1) u uD r hr hu).const_mul ((l+1 : ℕ) : ℂ)
  convert h1.sub h2 using 1
  · funext s
    simp only [profileD,profile,show l+1+1=l+2 by omega,mul_div_assoc]
  · simp only [profileDD,profileD,pow_succ]
    push_cast
    generalize he : (r : ℂ)^l = a
    have ha : a ≠ 0 := he ▸ pow_ne_zero l hrc
    ring_nf

theorem profile_radial_equation (l : ℕ) (u uD : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0) (q : ℂ) :
    profileDD l u uD (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*u r) r+
      (2*(l : ℂ)+2)/(r : ℂ)*profileD l u uD r+q^2*profile l u r=0 := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  simp only [profileDD,profileD,profile,pow_succ]
  push_cast
  generalize he : (r : ℂ)^l = a
  have ha : a ≠ 0 := he ▸ pow_ne_zero l hrc
  ring_nf

theorem profile_ode (l : ℕ) (u uD : ℝ → ℂ) (q : ℂ)
    (hu : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hud : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*u r) r)
    (r : ℝ) (hr : 0 < r) :
    deriv (deriv (profile l u)) r+(2*(l : ℂ)+2)/(r : ℂ)*deriv (profile l u) r+
      q^2*profile l u r=0 := by
  have hfirst := profile_hasDerivAt l u uD r hr.ne' (hu r hr)
  have he : deriv (profile l u) =ᶠ[𝓝 r] profileD l u uD := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact (profile_hasDerivAt l u uD s hs.ne' (hu s hs)).deriv
  have hsecond := (profileD_hasDerivAt l u uD r hr.ne' _ (hu r hr) (hud r hr)).congr_of_eventuallyEq he
  rw [hsecond.deriv,hfirst.deriv]
  exact profile_radial_equation l u uD r hr.ne' q

#print axioms OQ14.RadialQuotient.profile_hasDerivAt
#print axioms OQ14.RadialQuotient.profileD_hasDerivAt
#print axioms OQ14.RadialQuotient.profile_radial_equation
#print axioms OQ14.RadialQuotient.profile_ode

end OQ14.RadialQuotient

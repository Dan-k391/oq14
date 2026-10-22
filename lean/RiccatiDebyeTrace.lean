import DebyeRadialTrace
import RadialQuotient

/-! Exact actual Debye boundary fields in terms of a Riccati value and derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.RiccatiDebyeTrace
open Set OQ14.Maxwell OQ14.DebyeCalculus OQ14.DebyeRadialTrace OQ14.HarmonicPolynomial

def M (l : ℕ) (u : ℝ → ℂ) (p : Poly) : Field :=
  toroidal (scalar (RadialQuotient.profile l u) p)
def N (l : ℕ) (u : ℝ → ℂ) (p : Poly) : Field := curl (M l u p)

theorem profile_flux (l : ℕ) (u : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (uD : ℂ) (hu : HasDerivAt u uD r) :
    (r : ℂ)*deriv (RadialQuotient.profile l u) r+(l+1 : ℂ)*RadialQuotient.profile l u r=
      uD/(r : ℂ)^l := by
  rw [(RadialQuotient.profile_hasDerivAt l u (fun _ => uD) r hr hu).deriv]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  simp only [RadialQuotient.profile,RadialQuotient.profileD,pow_succ]
  push_cast
  generalize (r : ℂ)^l = a
  simp only [div_eq_mul_inv,mul_inv_rev]
  linear_combination (uD*a⁻¹-((l : ℂ)+1)*u r*a⁻¹*(r : ℂ)⁻¹)*mul_inv_cancel₀ hrc

theorem M_components (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    M l u p x i=u ‖x‖/(‖x‖ : ℂ)^(l+1)*angularToroidal p x i :=
  toroidal_components _ hu p x hx i

theorem M_cross (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    crossProduct (position x) (M l u p x) i=
      u ‖x‖/(‖x‖ : ℂ)^(l+1)*angularPoloidal p l x i :=
  toroidal_cross _ hu p l hp x hx i

theorem N_cross (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x ≠ 0) (uD : ℂ) (hd : HasDerivAt u uD ‖x‖) (i : Fin 3) :
    crossProduct (position x) (N l u p x) i= -(uD/(‖x‖ : ℂ)^l)*angularToroidal p x i := by
  rw [N,M,curl_cross _ hu p l hp hh x hx,
    profile_flux l u ‖x‖ (norm_ne_zero_iff.mpr hx) uD hd]

theorem M_radial (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) : dot (position x) (M l u p x)=0 :=
  toroidal_radial_zero _ hu p x hx

theorem N_radial (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x ≠ 0) :
    dot (position x) (N l u p x)=(l : ℂ)*(l+1)*(u ‖x‖/(‖x‖ : ℂ)^(l+1))*complexEvaluate p x :=
  curl_radial _ hu p l hp hh x hx

end OQ14.RiccatiDebyeTrace

#print axioms OQ14.RiccatiDebyeTrace.profile_flux
#print axioms OQ14.RiccatiDebyeTrace.M_components
#print axioms OQ14.RiccatiDebyeTrace.M_cross
#print axioms OQ14.RiccatiDebyeTrace.N_cross
#print axioms OQ14.RiccatiDebyeTrace.M_radial
#print axioms OQ14.RiccatiDebyeTrace.N_radial

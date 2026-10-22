import RiccatiTransmission
import SphericalScalarWaves

/-! Maxwell fields with the exact radial normalization used by layer transfers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RiccatiMaxwell
open Set OQ14.Maxwell OQ14.ModalDipole OQ14.HarmonicPolynomial
  OQ14.RiccatiTransmission OQ14.RiccatiDebyeTrace OQ14.DebyeCalculus

theorem scalar_smooth (l : ℕ) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (DebyeRadialTrace.scalar (RadialQuotient.profile l u) p) x :=
  (LocalRadialHarmonic.radial_smooth _ hu x hx).mul (complexEvaluate_regular p).contDiffAt

theorem scalar_helmholtz (l : ℕ) (u uD : ℝ → ℂ) (q : ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hdd : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*u r) r)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ExteriorHelmholtz.laplacian (DebyeRadialTrace.scalar (RadialQuotient.profile l u) p) x+
      q^2*DebyeRadialTrace.scalar (RadialQuotient.profile l u) p x=0 :=
  LocalRadialHarmonic.polynomial_helmholtz _ hu p l hp hh q
    (RadialQuotient.profile_ode l u uD q hd hdd) x hx

theorem te_maxwell (l : ℕ) (u uD : ℝ → ℂ) (q k ε : ℂ) (hk : k ≠ 0)
    (hdisp : q^2=k^2*ε)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hdd : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*u r) r)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (teE l u p) (teH l k u p) x :=
  DebyeMaxwell.te_maxwell isOpen_compl_singleton _
    (fun y hy => scalar_smooth l u hu p y hy) q k ε hk hdisp
    (fun y hy => scalar_helmholtz l u uD q hu hd hdd p hp hh y hy) x hx

theorem tm_maxwell (l : ℕ) (u uD : ℝ → ℂ) (q k ε : ℂ) (hε : ε ≠ 0)
    (hdisp : q^2=k^2*ε)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hdd : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*u r) r)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (tmE l ε u p) (tmH l k u p) x := by
  let f := DebyeRadialTrace.scalar (RadialQuotient.profile l u) p
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) f x := scalar_smooth l u hu p x hx
  have he := DebyeMaxwell.tm_maxwell isOpen_compl_singleton f
    (fun y hy => scalar_smooth l u hu p y hy) q k ε hdisp
    (fun y hy => scalar_helmholtz l u uD q hu hd hdd p hp hh y hy) x hx
  constructor
  · change curl (fun y j => ε⁻¹*N l u p y j) x = _
    rw [curl_const_mul (N l u p) x (ε⁻¹) (fun j =>
      (ExteriorClassical.curl_smooth _ (toroidal_smooth f x hs) j).differentiableAt (by simp))]
    have hc : curl (N l u p) x=fun j => Complex.I*k*(-Complex.I*k*ε*M l u p x j) := he.1
    rw [hc]
    ext j
    simp only [tmH,Pi.smul_apply,smul_eq_mul]
    field_simp [hε]
    ring
  · change curl (fun y j => (-Complex.I*k)*M l u p y j) x = _
    rw [curl_const_mul (M l u p) x (-Complex.I*k) (fun j => (toroidal_smooth f x hs j).differentiableAt (by simp))]
    ext j
    simp only [tmE,Pi.smul_apply,smul_eq_mul,N]
    field_simp [hε]
    ring

theorem te_real_maxwell (l : ℕ) (u uD : ℝ → ℂ) (q k ε : ℝ) (hk : k ≠ 0)
    (hdisp : q^2=k^2*ε)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hdd : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-(q : ℂ)^2)*u r) r)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (teE l u p) (teH l k u p) x := by
  have hdc : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    te_maxwell l u uD q k ε (Complex.ofReal_ne_zero.mpr hk) hdc hu hd hdd p hp hh x hx

theorem tm_real_maxwell (l : ℕ) (u uD : ℝ → ℂ) (q k ε : ℝ) (hε : ε ≠ 0)
    (hdisp : q^2=k^2*ε)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hd : ∀ r : ℝ, 0 < r → HasDerivAt u (uD r) r)
    (hdd : ∀ r : ℝ, 0 < r → HasDerivAt uD (((l : ℂ)*(l+1)/(r : ℂ)^2-(q : ℂ)^2)*u r) r)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (tmE l ε u p) (tmH l k u p) x := by
  have hdc : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    tm_maxwell l u uD q k ε (Complex.ofReal_ne_zero.mpr hε) hdc hu hd hdd p hp hh x hx

end OQ14.RiccatiMaxwell

#print axioms OQ14.RiccatiMaxwell.scalar_smooth
#print axioms OQ14.RiccatiMaxwell.scalar_helmholtz
#print axioms OQ14.RiccatiMaxwell.te_maxwell
#print axioms OQ14.RiccatiMaxwell.tm_maxwell
#print axioms OQ14.RiccatiMaxwell.te_real_maxwell
#print axioms OQ14.RiccatiMaxwell.tm_real_maxwell

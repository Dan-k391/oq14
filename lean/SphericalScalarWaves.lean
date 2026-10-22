import RadialQuotient
import RiccatiOriginSeries
import DebyeMaxwell

/-! Actual spherical scalar waves from the explicit regular and outgoing Riccati
functions, multiplied by genuine homogeneous harmonic polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.SphericalScalarWaves
open Set Filter OQ14.Maxwell OQ14.GreenKernel OQ14.ModalAlgebra OQ14.ModalWronskian
  OQ14.ModalMatching OQ14.ModalDipole OQ14.ExteriorHelmholtz OQ14.HarmonicPolynomial
open scoped Topology

def radialProfile (l : ℕ) (U : ℂ → ℂ) (q : ℂ) : ℝ → ℂ :=
  RadialQuotient.profile l (scaledRadial U q)

theorem radialProfile_smooth (l : ℕ) (U UD : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hU : ∀ z : ℂ, z ≠ 0 → HasDerivAt U (UD z) z) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialProfile l U q) (Ioi 0) := by
  have hd : DifferentiableOn ℂ U ({0}ᶜ : Set ℂ) :=
    fun z hz => (hU z hz).differentiableAt.differentiableWithinAt
  have hs : ContDiffOn ℂ (⊤ : ℕ∞) U ({0}ᶜ : Set ℂ) := hd.contDiffOn isOpen_compl_singleton
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => q*(r : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  intro r hr
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hu : ContDiffAt ℝ (⊤ : ℕ∞) (scaledRadial U q) r :=
    ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds (mul_ne_zero hq hrc))).restrict_scalars ℝ).comp r
      hscale.contDiffAt
  simpa only [radialProfile,RadialQuotient.profile,div_eq_mul_inv] using
    (hu.mul ((Complex.ofRealCLM.contDiff.pow (l+1)).contDiffAt.inv
      (pow_ne_zero _ hrc))).contDiffWithinAt

theorem scaled_second (l : ℕ) (U UD : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (hUD : HasDerivAt UD (((l : ℂ)*(l+1)/(q*r)^2-1)*U (q*r)) (q*r)) :
    HasDerivAt (scaledRadialD UD q)
      (((l : ℂ)*(l+1)/(r : ℂ)^2-q^2)*scaledRadial U q r) r := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  convert (hUD.scomp r ((complex_radius_hasDerivAt r).const_mul q)).const_mul q using 1
  simp only [smul_eq_mul,scaledRadial]
  field_simp [hrc,hq]
  ring

theorem radialProfile_ode (l : ℕ) (U UD : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hU : ∀ z : ℂ, z ≠ 0 → HasDerivAt U (UD z) z)
    (hUD : ∀ z : ℂ, z ≠ 0 → HasDerivAt UD (((l : ℂ)*(l+1)/z^2-1)*U z) z)
    (r : ℝ) (hr : 0 < r) :
    deriv (deriv (radialProfile l U q)) r+(2*(l : ℂ)+2)/(r : ℂ)*deriv (radialProfile l U q) r+
      q^2*radialProfile l U q r=0 := by
  apply RadialQuotient.profile_ode l (scaledRadial U q) (scaledRadialD UD q) q _ _ r hr
  · intro s hs
    exact scaledRadial_hasDerivAt U UD q s (hU _ (mul_ne_zero hq (Complex.ofReal_ne_zero.mpr hs.ne')))
  · intro s hs
    exact scaled_second l U UD q hq s hs.ne'
      (hUD _ (mul_ne_zero hq (Complex.ofReal_ne_zero.mpr hs.ne')))

def scalar (l : ℕ) (U : ℂ → ℂ) (q : ℂ) (p : Poly) (x : Space) : ℂ :=
  radialProfile l U q ‖x‖*complexEvaluate p x

theorem scalar_smooth (l : ℕ) (U UD : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hU : ∀ z : ℂ, z ≠ 0 → HasDerivAt U (UD z) z) (p : Poly) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (scalar l U q p) x :=
  (LocalRadialHarmonic.radial_smooth _ (radialProfile_smooth l U UD q hq hU) x hx).mul
    (complexEvaluate_regular p).contDiffAt

theorem scalar_helmholtz (l : ℕ) (U UD : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hU : ∀ z : ℂ, z ≠ 0 → HasDerivAt U (UD z) z)
    (hUD : ∀ z : ℂ, z ≠ 0 → HasDerivAt UD (((l : ℂ)*(l+1)/z^2-1)*U z) z)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    laplacian (scalar l U q p) x+q^2*scalar l U q p x=0 :=
  LocalRadialHarmonic.polynomial_helmholtz _ (radialProfile_smooth l U UD q hq hU)
    p l hp hh q (radialProfile_ode l U UD q hq hU hUD) x hx

theorem regular_helmholtz (l : ℕ) (q : ℂ) (hq : q ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    laplacian (scalar l (psi l) q p) x+q^2*scalar l (psi l) q p x=0 :=
  scalar_helmholtz l (psi l) (psiD l) q hq (psi_hasDerivAt l) (psiD_hasDerivAt l) p hp hh x hx

theorem outgoing_helmholtz (l : ℕ) (q : ℂ) (hq : q ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    laplacian (scalar l (xi l) q p) x+q^2*scalar l (xi l) q p x=0 :=
  scalar_helmholtz l (xi l) (xiD l) q hq (xi_hasDerivAt l) (xiD_hasDerivAt l) p hp hh x hx

end OQ14.SphericalScalarWaves

#print axioms OQ14.SphericalScalarWaves.radialProfile_smooth
#print axioms OQ14.SphericalScalarWaves.scaled_second
#print axioms OQ14.SphericalScalarWaves.radialProfile_ode
#print axioms OQ14.SphericalScalarWaves.scalar_smooth
#print axioms OQ14.SphericalScalarWaves.scalar_helmholtz
#print axioms OQ14.SphericalScalarWaves.regular_helmholtz
#print axioms OQ14.SphericalScalarWaves.outgoing_helmholtz

import SolidRadialSeries
import HelmholtzTestCalculus
import HarmonicPolynomial

/-! Actual globally smooth regular solid-harmonic Helmholtz waves. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SolidScalarHelmholtz

open Complex OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.SolidRadialSeries

def radial (l : ℕ) (q : ℂ) (t : ℝ) : ℂ := F l (q^2*(t : ℂ))

def wave (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly) (x : Space) : ℂ :=
  radial l q (‖x‖^2)*HarmonicPolynomial.complexEvaluate p x

theorem radial_contDiff (l : ℕ) (q : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (radial l q) := by
  exact ((F_contDiff l).restrict_scalars ℝ).comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => q^2*(t : ℂ)) from contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem radial_hasDerivAt (l : ℕ) (q : ℂ) (t : ℝ) :
    HasDerivAt (radial l q) (q^2*F1 l (q^2*(t : ℂ))) t := by
  have h := ((F_hasDerivAt l (q^2*(t : ℂ))).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (q^2))).comp_ofReal
  change HasDerivAt (fun r : ℝ => F l (q^2*(r : ℂ))) _ t
  convert h using 1
  ring

theorem radial_deriv (l : ℕ) (q : ℂ) :
    deriv (radial l q)=fun t : ℝ => q^2*F1 l (q^2*(t : ℂ)) :=
  funext (fun t => (radial_hasDerivAt l q t).deriv)

theorem radial_second_deriv (l : ℕ) (q : ℂ) (t : ℝ) :
    deriv (deriv (radial l q)) t=q^4*F2 l (q^2*(t : ℂ)) := by
  rw [radial_deriv]
  have h := (((F1_hasDerivAt l (q^2*(t : ℂ))).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (q^2))).const_mul (q^2)).comp_ofReal
  convert h.deriv using 1
  ring

theorem radial_ode (l : ℕ) (q : ℂ) (t : ℝ) :
    4*(t : ℂ)*deriv (deriv (radial l q)) t+(4*l+6 : ℂ)*deriv (radial l q) t+
      q^2*radial l q t=0 := by
  rw [radial_second_deriv,radial_deriv]
  dsimp only [radial]
  linear_combination q^2*normalized_ode l (q^2*(t : ℂ))

theorem wave_contDiff (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly) :
    ContDiff ℝ (⊤ : ℕ∞) (wave l q p) :=
  (HelmholtzTestCalculus.radial_smooth (radial l q) (radial_contDiff l q)).mul
    (HarmonicPolynomial.complexEvaluate_regular p)

theorem wave_helmholtz (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly)
    (hp : p.IsHomogeneous l) (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) :
    laplacian (wave l q p) x+q^2*wave l q p x=0 := by
  have hH : laplacian (HarmonicPolynomial.complexEvaluate p) x=0 := by
    rw [HarmonicPolynomial.complexEvaluate_laplacian,hh]
    simp [HarmonicPolynomial.evaluate]
  change laplacian (fun y => HelmholtzTestCalculus.radial (radial l q) y*
      HarmonicPolynomial.complexEvaluate p y) x+
        q^2*(HelmholtzTestCalculus.radial (radial l q) x*HarmonicPolynomial.complexEvaluate p x)=0
  rw [HelmholtzTestCalculus.radial_harmonic_laplacian (radial l q) (radial_contDiff l q)
    (HarmonicPolynomial.complexEvaluate p) x (HarmonicPolynomial.complexEvaluate_regular p).contDiffAt
    l hH (HarmonicPolynomial.complexEvaluate_euler p l hp x)]
  dsimp only [HelmholtzTestCalculus.radial]
  linear_combination HarmonicPolynomial.complexEvaluate p x*radial_ode l q (‖x‖^2)

theorem wave_zero (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly) :
    wave l q p 0=(RiccatiSeriesCoefficients.amplitude l 0 : ℂ)*HarmonicPolynomial.complexEvaluate p 0 := by
  simp only [wave,radial,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),Complex.ofReal_zero,mul_zero,F_zero]

theorem wave_regular_factor (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly)
    (hq : q ≠ 0) (x : Space) (hx : x ≠ 0) :
    wave l q p x=OQ14.ModalAlgebra.psi l (q*(‖x‖ : ℂ))/(q*(‖x‖ : ℂ))^(l+1)*
      HarmonicPolynomial.complexEvaluate p x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have he : q^2*((‖x‖^2 : ℝ) : ℂ)=(q*(‖x‖ : ℂ))^2 := by push_cast; ring
  rw [wave,radial,he,normalized_away l _ (mul_ne_zero hq hr)]

theorem wave_norm_bound (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly) (x : Space) :
    ‖wave l q p x‖ ≤ RiccatiSeriesCoefficients.amplitude l 0*
      Real.exp (‖q^2*((‖x‖^2 : ℝ) : ℂ)‖/2)*‖HarmonicPolynomial.complexEvaluate p x‖ := by
  rw [wave,norm_mul]
  exact mul_le_mul_of_nonneg_right (F_norm_bound l (q^2*((‖x‖^2 : ℝ) : ℂ)))
    (norm_nonneg (HarmonicPolynomial.complexEvaluate p x))

end OQ14.SolidScalarHelmholtz

#print axioms OQ14.SolidScalarHelmholtz.radial_contDiff
#print axioms OQ14.SolidScalarHelmholtz.radial_hasDerivAt
#print axioms OQ14.SolidScalarHelmholtz.radial_deriv
#print axioms OQ14.SolidScalarHelmholtz.radial_second_deriv
#print axioms OQ14.SolidScalarHelmholtz.radial_ode
#print axioms OQ14.SolidScalarHelmholtz.wave_contDiff
#print axioms OQ14.SolidScalarHelmholtz.wave_helmholtz
#print axioms OQ14.SolidScalarHelmholtz.wave_zero
#print axioms OQ14.SolidScalarHelmholtz.wave_regular_factor
#print axioms OQ14.SolidScalarHelmholtz.wave_norm_bound

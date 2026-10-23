import ToroidalPlaneWaveMoment
import VectorHarmonicNormalization

/-! Actual poloidal plane-wave coefficients obtained by differentiating the toroidal integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PoloidalPlaneWaveMoment
open Complex MeasureTheory Set MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.SphericalMomentEquation OQ14.SphereWaveCalculus OQ14.AngularHarmonicEnergy
open scoped Topology

private theorem polynomial_bound (p : Poly) (n : SphereReactionKernel.Sphere) :
    ‖angularPolynomial p n‖ ≤ ‖SpherePolynomial.polynomialMap p‖ := by
  simpa only [angularPolynomial,complexEvaluate,evaluate,Complex.norm_real,
    SpherePolynomial.polynomialMap_apply] using (SpherePolynomial.polynomialMap p).norm_coe_le_norm n

theorem polynomial_integrable (p : Poly) (k : ℝ) (x : Space) :
    Integrable (fun n => angularPolynomial p n*SphereReactionKernel.wave k x n)
      SphereReactionKernel.surface :=
  moment_integrable _ (angularPolynomial_continuous p) _ (polynomial_bound p) k x

theorem moment_sub (p q : Poly) (k : ℝ) (x : Space) :
    moment (angularPolynomial (p-q)) k x=
      moment (angularPolynomial p) k x-moment (angularPolynomial q) k x := by
  unfold moment
  rw [← integral_sub (polynomial_integrable p k x) (polynomial_integrable q k x)]
  apply integral_congr_ae
  filter_upwards with n
  simp [angularPolynomial,complexEvaluate,evaluate,sub_mul]

theorem polynomial_partial (p : Poly) (k : ℝ) (x : Space) (i : Fin 3) :
    dcoord (moment (angularPolynomial p) k) x i=
      (I*(k : ℂ))*moment (angularPolynomial (p*X i)) k x := by
  rw [moment_partial _ (angularPolynomial_continuous p) _ (polynomial_bound p)]
  congr 2
  funext n
  simp [angularPolynomial,complexEvaluate,evaluate]

theorem curl_polynomial_moments (Q : Fin 3 → Poly) (k : ℝ) (x : Space) (i : Fin 3) :
    Maxwell.curl (fun y j => moment (angularPolynomial (Q j)) k y) x i=
      -(I*(k : ℂ))*moment (angularPolynomial (PolynomialVectorCalculus.tor Q i)) k x := by
  fin_cases i <;> simp [Maxwell.curl,Maxwell.pd,polynomial_partial,
    PolynomialVectorCalculus.tor,moment_sub] <;> ring

theorem negative_toroidal_restriction (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (i : Fin 3) :
    angularPolynomial (PolynomialVectorCalculus.tor (toroidal p) i)=
      fun n => -angularPolynomial (tangential p l i) n := by
  have he : PolynomialVectorCalculus.radialDot (PolynomialVectorCalculus.grad p)=(l : ℝ) • p :=
    euler p l hp
  rw [← PolynomialVectorCalculus.tor_grad,PolynomialVectorCalculus.tor_tor,he]
  funext n
  have hs : evaluate radiusSq (n : Space)=1 := by
    have h := congrArg (fun f : C(SphereHarmonicBasis.Sphere,ℝ) => f n)
      FischerDecomposition.radiusSq_on_sphere
    simpa only [SpherePolynomial.polynomialMap_apply,ContinuousMap.one_apply,evaluate] using h
  simp [angularPolynomial,complexEvaluate,evaluate,tangential,PolynomialVectorCalculus.grad,
    smul_eq_C_mul,show MvPolynomial.eval (fun i => (n : Space) i) radiusSq=1 from hs]
  ring

theorem curl_toroidal_moment (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (k : ℝ) (x : Space) (i : Fin 3) :
    Maxwell.curl (fun y j => moment (angularPolynomial (toroidal p j)) k y) x i=
      (I*(k : ℂ))*moment (angularPolynomial (tangential p l i)) k x := by
  rw [curl_polynomial_moments,negative_toroidal_restriction p l hp]
  simp only [moment,neg_mul,integral_neg,mul_neg,neg_neg]

theorem scaled_polynomial_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (x : Space) (i : Fin 3) :
    (I*(k : ℂ))*moment (angularPolynomial (tangential p l i)) k x=
      (4*Real.pi : ℂ)*I^l*(k : ℂ)^l*
        DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i := by
  rw [← curl_toroidal_moment p l hp]
  have he : (fun y j => moment (angularPolynomial (toroidal p j)) k y)=
      fun y j => ((4*Real.pi : ℂ)*I^l*(k : ℂ)^l)*
        DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) y j := by
    funext y j
    exact ToroidalPlaneWaveMoment.polynomial_moment l p hp hh k y j
  rw [he,curl_const_mul _ x _ (fun j =>
    (DebyeCalculus.toroidal_smooth _ x (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt j).differentiableAt (by simp))]
  rfl

theorem polynomial_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (hk : k≠0) (x : Space) (i : Fin 3) :
    moment (angularPolynomial (tangential p l i)) k x=
      ((4*Real.pi : ℂ)*I^l*(k : ℂ)^l/(I*(k : ℂ)))*
        DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i := by
  have h := scaled_polynomial_moment l p hp hh k x i
  have hc : I*(k : ℂ)≠0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk)
  apply (mul_left_cancel₀ hc)
  rw [h]
  field_simp

theorem actual_poloidal_integral (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (hk : k≠0) (x : Space) (i : Fin 3) :
    (∫ n : SphereReactionKernel.Sphere,DebyeRadialTrace.angularPoloidal p l n i*
      SphereReactionKernel.wave k x n ∂SphereReactionKernel.surface)=
      ((4*Real.pi : ℂ)*I^l*(k : ℂ)^l/(I*(k : ℂ)))*
        DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i := by
  have he : (fun n : SphereReactionKernel.Sphere => DebyeRadialTrace.angularPoloidal p l n i)=
      angularPolynomial (tangential p l i) := by
    funext n
    simpa only [VectorHarmonicNormalization.restriction,SpherePolynomial.polynomialMap_apply,
      angularPolynomial,complexEvaluate,evaluate] using
      (VectorHarmonicNormalization.restriction_poloidal_component p l n i).symm
  simpa only [moment,← he] using polynomial_moment l p hp hh k hk x i

end OQ14.PoloidalPlaneWaveMoment
#print axioms OQ14.PoloidalPlaneWaveMoment.polynomial_integrable
#print axioms OQ14.PoloidalPlaneWaveMoment.moment_sub
#print axioms OQ14.PoloidalPlaneWaveMoment.polynomial_partial
#print axioms OQ14.PoloidalPlaneWaveMoment.curl_polynomial_moments
#print axioms OQ14.PoloidalPlaneWaveMoment.negative_toroidal_restriction
#print axioms OQ14.PoloidalPlaneWaveMoment.curl_toroidal_moment
#print axioms OQ14.PoloidalPlaneWaveMoment.scaled_polynomial_moment
#print axioms OQ14.PoloidalPlaneWaveMoment.polynomial_moment
#print axioms OQ14.PoloidalPlaneWaveMoment.actual_poloidal_integral

import ScalarPlaneWaveMoment
import PolynomialVectorCalculus

/-! Genuine toroidal plane-wave coefficients from harmonic polynomial moments. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ToroidalPlaneWaveMoment
open Complex MeasureTheory Filter Set MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.DebyeRadialTrace OQ14.SphericalMomentEquation OQ14.SphereWaveCalculus
open scoped Topology

theorem laplacian_X_mul (p : Poly) (i : Fin 3) :
    formalLaplacian (X i*p)=X i*formalLaplacian p+2*pderiv i p := by
  fin_cases i <;> simp [formalLaplacian_apply,Fin.sum_univ_three,pderiv_mul,pderiv_X] <;> ring

theorem toroidal_harmonic (p : Poly) (hh : formalLaplacian p=0) (i : Fin 3) :
    formalLaplacian (AngularHarmonicEnergy.toroidal p i)=0 := by
  have he (a b : Fin 3) : formalLaplacian (pderiv a p*X b)=2*pderiv b (pderiv a p) := by
    rw [mul_comm,laplacian_X_mul,PolynomialVectorCalculus.laplacian_pderiv,hh,map_zero,mul_zero,zero_add]
  fin_cases i <;> simp [AngularHarmonicEnergy.toroidal,he,AngularHarmonicEnergy.partial_commute]

theorem evaluate_toroidal (p : Poly) (x : Space) (i : Fin 3) :
    complexEvaluate (AngularHarmonicEnergy.toroidal p i) x=angularToroidal p x i := by
  fin_cases i <;> simp [AngularHarmonicEnergy.toroidal,angularToroidal,complexEvaluate_partial,
    complexEvaluate,evaluate]

theorem solid_toroidal_component (l : ℕ) (k : ℝ) (p : Poly) (x : Space) (i : Fin 3) :
    DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) x i=
      SolidScalarHelmholtz.wave l k (AngularHarmonicEnergy.toroidal p i) x := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => SolidScalarHelmholtz.radial l k (r^2)) :=
    (SolidScalarHelmholtz.radial_contDiff l k).comp (contDiff_id.pow 2)
  have he : (fun y => DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) y i)=
      SolidScalarHelmholtz.wave l k (AngularHarmonicEnergy.toroidal p i) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Space))
      (continuous_iff_continuousAt.mpr (fun y => (DebyeCalculus.toroidal_smooth _ y
        (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt i).continuousAt))
      (SolidScalarHelmholtz.wave_contDiff l k _).continuous
    intro y hy
    have hy0 : y≠0 := hy
    change DebyeCalculus.toroidal (scalar (fun r => SolidScalarHelmholtz.radial l k (r^2)) p) y i=_
    rw [toroidal_components _ hη.contDiffOn p y hy0 i]
    simp only [SolidScalarHelmholtz.wave,evaluate_toroidal]
  exact congrFun he x

theorem polynomial_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (y : Space) (i : Fin 3) :
    moment (angularPolynomial (AngularHarmonicEnergy.toroidal p i)) k y=
      (4*Real.pi : ℂ)*I^l*(k : ℂ)^l*
        DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) y i := by
  rw [ScalarPlaneWaveMoment.positive_moment l _ (AngularHarmonicEnergy.toroidal_homogeneous p l hp i)
    (toroidal_harmonic p hh i),solid_toroidal_component]

theorem actual_toroidal_integral (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (y : Space) (i : Fin 3) :
    (∫ n : SphereReactionKernel.Sphere,angularToroidal p n i*SphereReactionKernel.wave k y n
      ∂SphereReactionKernel.surface)=
      (4*Real.pi : ℂ)*I^l*(k : ℂ)^l*
        DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) y i := by
  have he : (fun n : SphereReactionKernel.Sphere => angularToroidal p n i)=
      angularPolynomial (AngularHarmonicEnergy.toroidal p i) := by
    funext n
    exact (evaluate_toroidal p n i).symm
  simpa only [moment,← he] using polynomial_moment l p hp hh k y i

end OQ14.ToroidalPlaneWaveMoment

#print axioms OQ14.ToroidalPlaneWaveMoment.laplacian_X_mul
#print axioms OQ14.ToroidalPlaneWaveMoment.toroidal_harmonic
#print axioms OQ14.ToroidalPlaneWaveMoment.evaluate_toroidal
#print axioms OQ14.ToroidalPlaneWaveMoment.solid_toroidal_component
#print axioms OQ14.ToroidalPlaneWaveMoment.polynomial_moment
#print axioms OQ14.ToroidalPlaneWaveMoment.actual_toroidal_integral

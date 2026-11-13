import ToroidalPlaneWaveMoment
import HarmonicMomentCoupling

/-! The finite harmonic degree-raising test used to select the outgoing physical
TM degree from the established Cartesian outgoing theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04RaisingPolynomial
open Complex MeasureTheory MvPolynomial OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.HarmonicPolynomial OQ14.AngularPower OQ14.DebyeRadialTrace
  OQ14.SphericalMomentEquation OQ14.HarmonicMomentCoupling

def raised (p : Poly) (l : ℕ) (i : Fin 3) : Poly :=
  X i * p - (2*(l : ℝ)+3)⁻¹ • (radiusSq * pderiv i p)

theorem raised_homogeneous (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous (l+1)) (i : Fin 3) :
    (raised p l i).IsHomogeneous (l+2) := by
  have hd : (pderiv i p).IsHomogeneous l := by simpa using hp.pderiv (i := i)
  have h1 : (X i * p).IsHomogeneous (l+2) := by
    convert (isHomogeneous_X ℝ i).mul hp using 1; omega
  have h2 : (radiusSq * pderiv i p).IsHomogeneous (l+2) := by
    convert radiusSq_homogeneous.mul hd using 1; omega
  exact (homogeneousSubmodule (Fin 3) ℝ (l+2)).sub_mem h1
    ((homogeneousSubmodule (Fin 3) ℝ (l+2)).smul_mem _ h2)

theorem raised_harmonic (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0) (i : Fin 3) :
    formalLaplacian (raised p l i) = 0 := by
  have hd : (pderiv i p).IsHomogeneous l := by simpa using hp.pderiv (i := i)
  have hdh : formalLaplacian (pderiv i p) = 0 := by
    rw [PolynomialVectorCalculus.laplacian_pderiv, hh, map_zero]
  have hc : 2*(l : ℝ)+3 ≠ 0 := by positivity
  rw [raised, map_sub, map_smul, ToroidalPlaneWaveMoment.laplacian_X_mul,
    homogeneous_radiusSq_mul _ l hd, hh, hdh]
  simp only [mul_zero, zero_add, add_zero, smul_eq_C_mul]
  have he : C ((2*(l : ℝ)+3)⁻¹) * C (4*(l : ℝ)+6) = (2 : Poly) := by
    rw [← map_mul]
    convert (map_ofNat (C : ℝ →+* Poly) 2) using 1
    congr 1
    field_simp [hc]
    ring
  rw [← mul_assoc, he, sub_self]

theorem raised_angular_value (p : Poly) (l : ℕ) (i : Fin 3) (ω : Sphere) :
    angularPolynomial (raised p l i) ω =
      radialWeight p i ω - ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ * gradientWeight p i ω := by
  have hR : evaluate radiusSq (ω : Space) = 1 := by
    have h := congrArg (fun f : C(Sphere, ℝ) => f ω) FischerDecomposition.radiusSq_on_sphere
    simpa only [SpherePolynomial.polynomialMap_apply, ContinuousMap.one_apply] using h
  simp only [angularPolynomial, raised, complexEvaluate, evaluate, map_sub,
    eval_mul, eval_X, smul_eq_C_mul, eval_C, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_inv, radialWeight, gradientWeight]
  change _ - (((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ *
    (((evaluate radiusSq (ω : Space) : ℝ) : ℂ) *
      ((evaluate (pderiv i p) (ω : Space) : ℝ) : ℂ))) = _
  rw [hR, Complex.ofReal_one, one_mul]
  rfl

end OQ14.Packet04RaisingPolynomial
#print axioms OQ14.Packet04RaisingPolynomial.raised_homogeneous
#print axioms OQ14.Packet04RaisingPolynomial.raised_harmonic
#print axioms OQ14.Packet04RaisingPolynomial.raised_angular_value

import ToroidalPlaneWaveMoment
import ModalDipoleAngularGeometry

noncomputable section
set_option autoImplicit false
namespace OQ14.DipoleQuadraticMoments
open MvPolynomial OQ14.HarmonicPolynomial OQ14.Maxwell

def quadratic (i : Fin 3) : Poly := C (3 : ℝ) * (X i * X 2) - (if i = 2 then radiusSq else 0)

theorem quadratic_homogeneous (i : Fin 3) : (quadratic i).IsHomogeneous 2 := by
  have h : (C (3 : ℝ) * (X i * X 2) : Poly).IsHomogeneous 2 := by
    simpa [smul_eq_C_mul] using (homogeneousSubmodule (Fin 3) ℝ 2).smul_mem (3 : ℝ)
      (by simpa using (isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ (2 : Fin 3)))
  unfold quadratic
  split_ifs
  · exact (homogeneousSubmodule (Fin 3) ℝ 2).sub_mem h radiusSq_homogeneous
  · simpa using h

theorem quadratic_harmonic (i : Fin 3) : formalLaplacian (quadratic i) = 0 := by
  have h2 (j : Fin 3) : pderiv j (2 : Poly) = 0 := by change pderiv j (C (2 : ℝ)) = 0; exact pderiv_C
  have h3 (j : Fin 3) : pderiv j (3 : Poly) = 0 := by change pderiv j (C (3 : ℝ)) = 0; exact pderiv_C
  have hC : C (3 : ℝ) = (3 : Poly) := map_ofNat C 3
  fin_cases i <;> (simp [quadratic, radiusSq, formalLaplacian_apply, Fin.sum_univ_three, pderiv_mul, pderiv_X, pderiv_C, h2, h3, hC]; try norm_num)

#print axioms OQ14.DipoleQuadraticMoments.quadratic_homogeneous
#print axioms OQ14.DipoleQuadraticMoments.quadratic_harmonic
end OQ14.DipoleQuadraticMoments

namespace OQ14.DipoleQuadraticMoments
open MvPolynomial OQ14.HarmonicPolynomial OQ14.Maxwell OQ14.AngularPower

theorem quadratic_on_sphere (i : Fin 3) (ω : Sphere) :
    SphericalMomentEquation.angularPolynomial (quadratic i) ω =
      3 * (((ω : Space) i : ℝ) : ℂ) * (((ω : Space) 2 : ℝ) : ℂ) -
        (if i = 2 then 1 else 0) := by
  have hn := GreenKernel.coordinate_squares (ω : Space)
  rw [sphere_norm] at hn
  fin_cases i <;> simp [SphericalMomentEquation.angularPolynomial, quadratic, complexEvaluate,
    evaluate, radiusSq, Fin.sum_univ_three, hn] <;> ring_nf

#print axioms OQ14.DipoleQuadraticMoments.quadratic_on_sphere
end OQ14.DipoleQuadraticMoments

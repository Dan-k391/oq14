import ComplexKernelRadialBasis
import WeakRegularBallBasis

/-! Regular-origin selection for every actual complex sphere volume-kernel vector. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexKernelRegularOrigin
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakHelmholtzRegularity
abbrev VectorL2 := VectorFourier.VectorL2

theorem interior_ball (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) :
    IsWeakHelmholtz (z*n) (ball 0 1)
      (NewtonL2.physicalCoordinate (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i) :=
  ComplexKernelRadialBasis.weak_congr_ae (z*n) (ball 0 1) _ _
    (NewtonL2.physicalCoordinate_ae (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i)
    (ComplexSphereHelmholtz.actual_weak_helmholtz n hn z hz u hker i)

theorem regular_moment (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i)
        (SphericalMomentEquation.angularPolynomial p) r =
      c * RadialOriginSelection.regular l (z*n) r := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact WeakRegularBallBasis.moment_expansion 1 a b ha hb (by norm_num) (z*n)
    (mul_ne_zero hz hn0) _ (interior_ball n hn z hz u hker i) p l hp hh

end OQ14.ComplexKernelRegularOrigin
#print axioms OQ14.ComplexKernelRegularOrigin.interior_ball
#print axioms OQ14.ComplexKernelRegularOrigin.regular_moment

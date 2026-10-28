import RegularModeGluing
import ComplexKernelRegularOrigin

/-! One regular amplitude on the entire interior for actual weak fields and sphere kernels. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.RegularBallGlobal
open Complex MeasureTheory Metric Set OQ14.Maxwell

theorem weak_moment (L : ℝ) (hL : 0 < L) (k : ℂ) (hk : k ≠ 0)
    (u : PolarMomentEnergy.ScalarL2)
    (hw : WeakHelmholtzRegularity.IsWeakHelmholtz k (ball 0 L) u)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 L),
      (r : ℂ) * RadialMoment.moment u (SphericalMomentEquation.angularPolynomial p) r =
        c * RadialOriginSelection.regular l k r :=
  RegularModeGluing.glue L hL l k hk _ (fun a b ha hb =>
    WeakRegularBallBasis.moment_expansion L a b ha hb hL k hk u hw p l hp hh)

theorem kernel_moment (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 1),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i)
        (SphericalMomentEquation.angularPolynomial p) r =
      c * RadialOriginSelection.regular l (z*n) r := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact weak_moment 1 (by norm_num) (z*n) (mul_ne_zero hz hn0) _
    (ComplexKernelRegularOrigin.interior_ball n hn z hz u hker i) p l hp hh

end OQ14.RegularBallGlobal
#print axioms OQ14.RegularBallGlobal.weak_moment
#print axioms OQ14.RegularBallGlobal.kernel_moment

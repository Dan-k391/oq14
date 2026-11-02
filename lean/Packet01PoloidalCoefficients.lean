import Packet01RadialTestReduction
import Packet01MomentIntegrability
import Packet01WeakDerivative

/-! The same radial and tangential amplitude for the actual sphere-kernel field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.Packet01PoloidalCoefficients
open Complex MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentCoupling
  OQ14.HarmonicMomentIntegrability OQ14.ComplexKernelResponse
open scoped Topology

theorem tangential_of_radial
    (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (c : ℂ)
    (hc : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r =
        c * RadialOriginSelection.regular (l+1) (z*n) r) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r =
        c * RadialOriginSelection.regularD (l+1) (z*n) r / (r : ℂ) := by
  have hk : z * (n : ℂ) ≠ 0 :=
    mul_ne_zero hz (Complex.ofReal_ne_zero.mpr (by linarith))
  have hg := (Packet01MomentIntegrability.weighted_tangentialMoment_locallyIntegrableOn
    (ComplexKernelDebye.coordinates n hn z u) p l).mono_set
    (show Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hw := Packet01WeakDerivative.of_complex_tests (Ioo (0 : ℝ) 1)
    (fun r => (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r)
    (fun r => (r : ℂ) * tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r)
    (Packet01RadialTestReduction.actual_radial_tangential_weak n hn z hz u hker p l hp)
  have hid := Packet01WeakDerivative.identify_regular_derivative (l+1) (z*n) c hk
    (fun r => (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r)
    (fun r => (r : ℂ) * tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r)
    hc hg hw
  filter_upwards [hid, ae_restrict_mem measurableSet_Ioo] with r hr hri
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hri.1.ne')).mpr
  simpa only [mul_comm] using hr

theorem electric_radial_tangential_regular
    (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ((r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r =
        c * RadialOriginSelection.regular (l+1) (z*n) r) ∧
      (tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r =
        c * RadialOriginSelection.regularD (l+1) (z*n) r / (r : ℂ)) := by
  obtain ⟨c, hc⟩ := ComplexKernelDebye.regular_radial_coefficient n hn z hz u hker
    p (l+1) hp hh
  refine ⟨c, ?_⟩
  filter_upwards [hc, tangential_of_radial n hn z hz u hker p l hp c hc] with r hr ht
  exact ⟨hr, ht⟩

theorem electric_radial_tangential_actual
    (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ((r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r =
        c * RadialOriginSelection.regular (l+1) (z*n) r) ∧
      ((∫ ω : Sphere, ∑ j : Fin 3,
        response (ModalWeightedMode.coefficient n hn) z 1 u
          (VectorFourier.coordinateMap (r • (ω : Space))) j *
          (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω) ∂angularMeasure) =
        c * RadialOriginSelection.regularD (l+1) (z*n) r / (r : ℂ)) := by
  obtain ⟨c, hc⟩ := electric_radial_tangential_regular n hn z hz u hker p l hp hh
  refine ⟨c, ?_⟩
  filter_upwards [hc, KernelRadialMomentBridge.tangential_moment_actual n hn z u p l] with r hr ht
  exact ⟨hr.1, ht.symm.trans hr.2⟩

end OQ14.Packet01PoloidalCoefficients
#print axioms OQ14.Packet01PoloidalCoefficients.tangential_of_radial
#print axioms OQ14.Packet01PoloidalCoefficients.electric_radial_tangential_regular
#print axioms OQ14.Packet01PoloidalCoefficients.electric_radial_tangential_actual

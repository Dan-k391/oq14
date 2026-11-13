import HarmonicMomentIntegrability
import ComplexKernelDebye

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OQ14.KernelRadialMomentBridge
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolarMomentTesting OQ14.PolarMomentEnergy
  OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
  OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

theorem radial_moment_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (p : HarmonicPolynomial.Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      radialMoment (ComplexKernelDebye.coordinates n hn z u) p r =
        ComplexKernelDebye.radialCoefficient n hn z u p r := by
  let E := response (ModalWeightedMode.coefficient n hn) z 1 u
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun r hr => hr.1
  trace "before hi"
  have hi : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ j : Fin 3,
      Integrable (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω) angularMeasure := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [slice_memLp_ae (NewtonL2.physicalCoordinate E j)] with r hr
    exact hr.integrable_mul (weight_memLp p j).1
  trace "before hj"
  have hj (j : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ ω : Sphere ∂angularMeasure,
      NewtonL2.physicalCoordinate E j (r • (ω : Space)) =
        E (VectorFourier.coordinateMap (r • (ω : Space))) j := by
    have hcoord : ∀ᵐ x : Space ∂volume, NewtonL2.physicalCoordinate E j x = E (VectorFourier.coordinateMap x) j := NewtonL2.physicalCoordinate_ae E j
    exact OQ14.PolarMomentAE.polar_ae hcoord
  trace "before he"
  have he : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ ω : Sphere ∂angularMeasure,
      ∀ j : Fin 3, NewtonL2.physicalCoordinate E j (r • (ω : Space)) =
        E (VectorFourier.coordinateMap (r • (ω : Space))) j := by
    filter_upwards [ae_all_iff.mpr hj] with r hr
    exact ae_all_iff.mpr hr
  trace "before filter"
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hi,
    ae_restrict_of_ae_restrict_of_subset hsub he] with r hr he
  trace "before hs"
  have hs : (∑ j : Fin 3, ∫ ω : Sphere, NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω ∂angularMeasure) =
      ComplexKernelDebye.radialCoefficient n hn z u p r := by
    rw [← integral_finset_sum _ (fun j _ => hr j)]
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    change (∑ j : Fin 3, NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω) =
      (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) * E (VectorFourier.coordinateMap (r • (ω : Space))) j) *
        SphericalMomentEquation.angularPolynomial p ω
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hω j]
    dsimp [radialWeight]
    ring
  exact hs

#print axioms OQ14.KernelRadialMomentBridge.radial_moment_actual
end OQ14.KernelRadialMomentBridge

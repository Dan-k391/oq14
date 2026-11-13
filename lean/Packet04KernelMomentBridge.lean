import Packet04PolynomialCoordinates
import Packet04KernelRecovery
import Packet01PoloidalCoefficients

/-! Actual weighted volume-kernel angular coordinates coincide with the
physical electric moments inside the material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04KernelMomentBridge
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability OQ14.ComplexKernelResponse
  OQ14.ModalVectorAngularSlices OQ14.Packet04PolynomialCoordinates

theorem slice_recovery (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      (slice u r : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure]
        fun ω => (Real.sqrt (n^2-1) : ℂ) •
          response (ModalWeightedMode.coefficient n hn) z 1 u
            (VectorFourier.coordinateMap (r • (ω : Space))) := by
  have hs : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := Ioo_subset_Ioi_self
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (slice_actual_ae u),
    ae_restrict_of_ae_restrict_of_subset hs (PolarMomentAE.polar_ae
      (kernel_coordinate_ae (ModalWeightedMode.coefficient n hn) z 1 u hker)),
    ae_restrict_mem measurableSet_Ioo] with r hu hk hr
  filter_upwards [hu, hk] with ω hu hk
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr.1]
  rw [hu, hk, ModalWeightedMode.coefficient_value, hnorm, if_pos hr.2]

theorem weighted_moment (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (w : Sphere → Fin 3 → ℂ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      (∫ ω : Sphere, ∑ j : Fin 3, slice u r ω j * w ω j ∂angularMeasure) =
      (Real.sqrt (n^2-1) : ℂ) * (∫ ω : Sphere, ∑ j : Fin 3,
        response (ModalWeightedMode.coefficient n hn) z 1 u
          (VectorFourier.coordinateMap (r • (ω : Space))) j * w ω j ∂angularMeasure) := by
  filter_upwards [slice_recovery n hn z u hker] with r hr
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hr] with ω hω
  rw [hω, Finset.mul_sum]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc]

theorem radial_coordinate_actual (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      radialCoordinate (slice u r) p = (Real.sqrt (n^2-1) : ℂ) *
        ComplexKernelDebye.radialCoefficient n hn z u p r := by
  filter_upwards [weighted_moment n hn z u hker (fun ω j => radialWeight p j ω)] with r hr
  rw [Packet04PolynomialCoordinates.radial_actual, hr]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  simp only [radialWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem poloidal_coordinate_actual (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (p : Poly) (l : ℕ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      poloidalCoordinate (slice u r) (l+1) p = (Real.sqrt (n^2-1) : ℂ) *
        tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r := by
  filter_upwards [weighted_moment n hn z u hker
      (fun ω j => gradientWeight p j ω - (l+1 : ℂ)*radialWeight p j ω),
    KernelRadialMomentBridge.tangential_moment_actual n hn z u p l] with r hr ht
  rw [poloidal_actual]
  push_cast
  rw [hr, ht]

theorem toroidal_coordinate_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), toroidalCoordinate (slice u r) p = 0 := by
  have he : ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 1 u =
      response (ModalWeightedMode.coefficient n hn) z 1 u := by
    simp only [ComplexExteriorResponse.response, response, mul_one, one_add_one_eq_two]
  have hz := Packet04ToroidalMoments.actual_toroidal_zero n hn z 1 le_rfl u hu hker p l hp
  simp only [ComplexSphereMaxwell.electric, he] at hz
  filter_upwards [weighted_moment n hn z u hker
    (fun ω j => DebyeRadialTrace.angularToroidal p (ω : Space) j), hz] with r hr hz
  rw [toroidal_actual, hr, hz, mul_zero]

end OQ14.Packet04KernelMomentBridge
#print axioms OQ14.Packet04KernelMomentBridge.slice_recovery
#print axioms OQ14.Packet04KernelMomentBridge.weighted_moment
#print axioms OQ14.Packet04KernelMomentBridge.radial_coordinate_actual
#print axioms OQ14.Packet04KernelMomentBridge.poloidal_coordinate_actual
#print axioms OQ14.Packet04KernelMomentBridge.toroidal_coordinate_zero

import ModalVolumeAngularCoefficients
import ModalVectorAngularSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ModalAngularPairing
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.ModalVolumeAngularCoefficients
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem coefficient_integral (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), coefficient u m r =
      ∫ ω : Sphere, ∑ i : Fin 3, DynamicConvolution.component i u (r • (ω : Space)) * weight m i ω ∂angularMeasure := by
  have hi : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      Integrable (fun ω : Sphere => DynamicConvolution.component i u (r • (ω : Space)) * weight m i ω) angularMeasure := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [slice_memLp_ae (DynamicConvolution.component i u)] with r hr
    exact hr.integrable_mul (weight_memLp m i)
  filter_upwards [hi] with r hr
  unfold coefficient moment
  exact (integral_finset_sum _ (fun i _ => hr i)).symm

#print axioms OQ14.ModalAngularPairing.coefficient_integral

end OQ14.ModalAngularPairing



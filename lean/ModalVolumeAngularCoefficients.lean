import ModalDipoleAngularGeometry
import ModalAngularSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalVolumeAngularCoefficients
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.PolarMomentEnergy OQ14.PolarMomentTesting
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

def weight (m : C(Sphere, ComplexVectorSphere.Vector)) (i : Fin 3) (ω : Sphere) : ℂ :=
  star (m ω i)

theorem weight_continuous (m : C(Sphere, ComplexVectorSphere.Vector)) (i : Fin 3) :
    Continuous (weight m i) := by
  simpa [weight, Function.comp_def] using Complex.continuous_conj.comp ((EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).continuous.comp m.continuous)

theorem weight_memLp (m : C(Sphere, ComplexVectorSphere.Vector)) (i : Fin 3) :
    MemLp (weight m i) 2 angularMeasure := by
  apply (weight_continuous m i).memLp_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

def coefficient (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (DynamicConvolution.component i u) (weight m i) r

theorem coefficient_weighted_memLp (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    MemLp (fun r : ℝ => (r : ℂ)*coefficient u m r) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have h (i : Fin 3) := radial_moment_memLp (DynamicConvolution.component i u) (weight m i)
    (weight_continuous m i).measurable (weight_memLp m i)
  have hs := (h 0).add (h 1) |>.add (h 2)
  convert hs using 1
  funext r
  simp [coefficient, Fin.sum_univ_three, mul_add]

#print axioms OQ14.ModalVolumeAngularCoefficients.coefficient_weighted_memLp
end OQ14.ModalVolumeAngularCoefficients





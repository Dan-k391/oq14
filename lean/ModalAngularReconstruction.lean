import ModalRadialLift
noncomputable section
set_option autoImplicit false
namespace OQ14.ModalAngularReconstruction
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.PolarMomentEnergy
  OQ14.ModalVolumeAngularCoefficients

theorem coefficient_stronglyMeasurable (u : VectorFourier.VectorL2)
    (m : C(Sphere, ComplexVectorSphere.Vector)) : StronglyMeasurable (coefficient u m) := by
  unfold coefficient
  apply Finset.stronglyMeasurable_sum
  intro i _
  exact moment_stronglyMeasurable (DynamicConvolution.component i u) (weight m i) (weight_continuous m i).measurable

theorem radial_coefficient_spatial_memLp (u : VectorFourier.VectorL2)
    (m : C(Sphere, ComplexVectorSphere.Vector)) :
    MemLp (fun x : Space => coefficient u m ‖x‖) 2 volume :=
  ModalRadialLift.radial_memLp (coefficient u m) (coefficient_stronglyMeasurable u m)
    (coefficient_weighted_memLp u m)

def reconstructedField (u : VectorFourier.VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) (x : Space) :
    ComplexVectorSphere.Vector := coefficient u m ‖x‖ • m (ConicalCapField.unit x)

theorem reconstructedField_memLp (u : VectorFourier.VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    MemLp (reconstructedField u m) 2 volume := by
  have hg := radial_coefficient_spatial_memLp u m
  have hm : StronglyMeasurable (fun x : Space => m (ConicalCapField.unit x)) :=
    m.continuous.stronglyMeasurable.comp_measurable ConicalCapField.unit_measurable
  have hmeas : AEStronglyMeasurable (reconstructedField u m) volume :=
    hg.aestronglyMeasurable.smul hm.aestronglyMeasurable
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn m.continuous.continuousOn
  apply hg.of_le_mul (c := C) hmeas
  filter_upwards with x
  change ‖coefficient u m ‖x‖ • m (ConicalCapField.unit x)‖ ≤ C * ‖coefficient u m ‖x‖‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC _ (Set.mem_univ _)) (norm_nonneg _)

def reconstruct (u : VectorFourier.VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) : VectorFourier.VectorL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ VectorFourier.coordinateMap.symm VectorFourier.coordinateMap_preserving.symm
    ((reconstructedField_memLp u m).toLp (reconstructedField u m))

theorem reconstruct_actual (u : VectorFourier.VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    (fun x : Space => reconstruct u m (VectorFourier.coordinateMap x)) =ᵐ[volume] reconstructedField u m := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving ((reconstructedField_memLp u m).toLp (reconstructedField u m))
      VectorFourier.coordinateMap_preserving.symm)
  filter_upwards [h, (reconstructedField_memLp u m).coeFn_toLp] with x h1 h2
  simpa [reconstruct] using h1.trans h2

#print axioms OQ14.ModalAngularReconstruction.reconstruct_actual
#print axioms OQ14.ModalAngularReconstruction.reconstructedField_memLp
#print axioms OQ14.ModalAngularReconstruction.coefficient_stronglyMeasurable
#print axioms OQ14.ModalAngularReconstruction.radial_coefficient_spatial_memLp
end OQ14.ModalAngularReconstruction



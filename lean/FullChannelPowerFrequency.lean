import FullChannelFinal

/-! Power-normalized frequency dilation for every actual angular input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelPowerFrequency
open Maxwell MaterialMaxwell FrequencyScalingMaxwell

/-- The full material solution, with the k amplitude factor required to preserve
    physical incoming and outgoing channel powers, solves the frequency-k system. -/
theorem power_scaled_material_maxwell (k : ℝ) (hk : 0 < k)
    (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) :
    TestMaxwell k (dielectric (scaleCoeff k c))
      (scaleField k (MaterialField.total c 1 (FullChannelTEMatch.normalizedSolution c d F hF)
        (FullChannelTEMatch.normalizedElectric F)))
      (scaleField k (totalMagnetic c 1 (FullChannelTEMatch.normalizedSolution c d F hF)
        (FullChannelMaterialMaxwell.normalizedMagnetic F))) :=
  testMaxwell_scaleCoeff k hk c _ _ (FullChannelMaterialMaxwell.normalized_material_maxwell c d F hF hu)

end OQ14.FullChannelPowerFrequency
#print axioms OQ14.FullChannelPowerFrequency.power_scaled_material_maxwell

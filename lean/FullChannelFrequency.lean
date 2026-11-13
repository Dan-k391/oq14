import FullChannelMaterialMaxwell
import FrequencyScalingPower

/-! Exact frequency dilation of the actual full-angular Herglotz illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelFrequency
open Maxwell

/-- The Herglotz evaluation at frequency k is the frequency-one evaluation
    at the physically dilated point. This holds for arbitrary angular L² data. -/
theorem value_dilation (k : ℝ) (x : Maxwell.Space) (i : Fin 3)
    (F : ComplexVectorSphere.Ambient) :
    HerglotzAngularL2.value (-k) x i F = HerglotzAngularL2.value (-1) (k • x) i F := by
  have hp : TransversePlaneFields.plane k x i = TransversePlaneFields.plane 1 (k • x) i := by
    ext n j
    simp only [TransversePlaneFields.plane, ContinuousMap.coe_mk, PiLp.smul_apply, smul_eq_mul]
    congr 1
    unfold SphereReactionKernel.wave
    congr 1
    simp only [inner_smul_right, RCLike.conj_to_real, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one]
    ring
  have hf : TransversePlaneFields.field k x i = TransversePlaneFields.field 1 (k • x) i := by
    unfold TransversePlaneFields.field
    rw [hp]
  unfold HerglotzAngularL2.value
  simp only [neg_neg]
  rw [hf]

/-- Physical incident electric field at frequency k obtained by spatial dilation. -/
def electricAt (k : ℝ) (F : ComplexVectorSphere.Ambient) : Maxwell.Field := fun x i =>
  ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) * HerglotzAngularL2.value (-k) x i F

/-- Physical incident magnetic field at frequency k, including the convention sign. -/
def magneticAt (k : ℝ) (F : ComplexVectorSphere.Ambient) : Maxwell.Field := fun x i =>
  -((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) * FullChannelMagnetic.magnetic (-k) F x i

theorem electricAt_dilation (k : ℝ) (F : ComplexVectorSphere.Ambient) (x : Maxwell.Space) (i : Fin 3) :
    electricAt k F x i = FullChannelTEMatch.normalizedElectric F (k • x) i := by
  unfold electricAt FullChannelTEMatch.normalizedElectric
  rw [value_dilation k x i F]

theorem magneticAt_dilation (k : ℝ) (F : ComplexVectorSphere.Ambient) (x : Maxwell.Space) (i : Fin 3) :
    magneticAt k F x i = FullChannelMaterialMaxwell.normalizedMagnetic F (k • x) i := by
  unfold magneticAt FullChannelMaterialMaxwell.normalizedMagnetic FullChannelMagnetic.magnetic
  rw [value_dilation k x i (-FullChannelMagnetic.rotation F)]

/-- All-input actual material Maxwell fields scale to any positive physical frequency. -/
theorem material_maxwell_at_frequency (k : ℝ) (hk : 0 < k)
    (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) :
    MaterialMaxwell.TestMaxwell k
      (MaterialMaxwell.dielectric (FrequencyScalingMaxwell.scaleCoeff k c))
      (PuncturedMaxwellScaling.fieldAtFrequency k
        (MaterialField.total c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (FullChannelTEMatch.normalizedElectric F)))
      (PuncturedMaxwellScaling.fieldAtFrequency k
        (MaterialMaxwell.totalMagnetic c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (FullChannelMaterialMaxwell.normalizedMagnetic F))) := by
  have hm := FrequencyScalingMaxwell.testMaxwell_scale k hk (MaterialMaxwell.dielectric c) _ _
    (FullChannelMaterialMaxwell.normalized_material_maxwell c d F hF hu)
  rw [FrequencyScalingMaxwell.dielectric_scaleCoeff_eq]
  exact hm

/-- The power-normalized frequency-k incident fields are the amplitude-normalized
    dilations of the complete transverse L² incident fields. -/
theorem scaled_incident_electric (k : ℝ) (F : ComplexVectorSphere.Ambient)
    (x : Maxwell.Space) (i : Fin 3) :
    FrequencyScalingMaxwell.scaleField k (FullChannelTEMatch.normalizedElectric F) x i =
      (k : ℂ) * electricAt k F x i := by
  rw [electricAt_dilation]
  rfl

theorem scaled_incident_magnetic (k : ℝ) (F : ComplexVectorSphere.Ambient)
    (x : Maxwell.Space) (i : Fin 3) :
    FrequencyScalingMaxwell.scaleField k (FullChannelMaterialMaxwell.normalizedMagnetic F) x i =
      (k : ℂ) * magneticAt k F x i := by
  rw [magneticAt_dilation]
  rfl

/-- For every angular L² input, the actual compact-source radiated far amplitude
    is invariant under the power-normalized frequency dilation. -/
theorem radiated_far_at_frequency (k : ℝ) (hk : 0 < k)
    (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (n : Maxwell.Space) (hn : ‖n‖ = 1) :
    Filter.Tendsto (fun r : ℝ => MaxwellFarField.factor k r •
      FrequencyScalingMaxwell.scaleField k
        (ExteriorContinuity.electric 1 (DynamicVolume.source c (FullChannelTEMatch.normalizedSolution c d F hF)))
        (r • n)) Filter.atTop
      (nhds (MaxwellFarField.electricAmplitude 1
        (DynamicVolume.source c (FullChannelTEMatch.normalizedSolution c d F hF)) n)) := by
  apply FrequencyScalingPower.scattered_far_scale k hk (max d.radius 0) (le_max_right _ _)
  · exact DynamicVolume.source_integrable c _ d.radius d.ballZero
  · intro j y hy
    exact DynamicVolume.source_zero c _ d.radius d.ballZero j y
      (fun h => hy (Metric.closedBall_subset_closedBall (le_max_left _ _) h))
  · exact hn

end OQ14.FullChannelFrequency
#print axioms OQ14.FullChannelFrequency.value_dilation

#print axioms OQ14.FullChannelFrequency.electricAt_dilation
#print axioms OQ14.FullChannelFrequency.magneticAt_dilation
#print axioms OQ14.FullChannelFrequency.material_maxwell_at_frequency

#print axioms OQ14.FullChannelFrequency.scaled_incident_electric
#print axioms OQ14.FullChannelFrequency.scaled_incident_magnetic
#print axioms OQ14.FullChannelFrequency.radiated_far_at_frequency

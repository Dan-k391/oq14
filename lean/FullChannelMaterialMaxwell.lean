import FullChannelWeakLimit
import FrequencyScalingMaxwell

/-! Actual Maxwell fields for arbitrary normalized angular input and compact dielectric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelMaterialMaxwell
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse
open FrequencyScalingMaxwell

/-- The physical magnetic incident field, with the sign required by the
    negative-frequency Herglotz convention and the incoming-power normalization. -/
def normalizedMagnetic (F : ComplexVectorSphere.Ambient) : Maxwell.Field := fun x i =>
  -((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) * FullChannelMagnetic.magnetic (-1) F x i

/-- The normalized general angular input is a genuine frequency-one vacuum Maxwell field. -/
theorem normalized_incident_maxwell (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) :
    TestMaxwell 1 (fun _ => 1) (FullChannelTEMatch.normalizedElectric F) (normalizedMagnetic F) := by
  let E : Maxwell.Field := fun x i => HerglotzAngularL2.value (-1) x i F
  let H : Maxwell.Field := FullChannelMagnetic.magnetic (-1) F
  have hm := FullChannelWeakLimit.herglotz_testMaxwell (-1) F hF
  have hp (G : Maxwell.Field) (j : Fin 3) (f : Test) :
      fieldPair (fun x i => -G x i) j f = -fieldPair G j f := by
    simp only [fieldPair, neg_mul, integral_neg]
  have hc (G : Maxwell.Field) (j : Fin 3) (f : Test) :
      curlPair (fieldPair (fun x i => -G x i)) j f = -curlPair (fieldPair G) j f := by
    unfold curlPair
    rw [hp, hp]
    ring
  have hn : TestMaxwell 1 (fun _ => 1) E (fun x i => -H x i) := by
    intro i f
    obtain ⟨h1, h2⟩ := hm i f
    change curlPair (fieldPair E) i f = Complex.I * (1 : ℂ) * fieldPair (fun x i => -H x i) i f ∧
      curlPair (fieldPair (fun x i => -H x i)) i f =
        -(Complex.I * (1 : ℂ)) * (∫ x, (1 : ℂ) * E x i * f.val x)
    rw [hp, hc]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one,
      one_mul, neg_mul] at h1 h2 ⊢
    constructor
    · exact h1
    · change -curlPair (fieldPair H) i f = -(Complex.I * fieldPair E i f)
      change curlPair (fieldPair H) i f = - -(Complex.I * fieldPair E i f) at h2
      rw [h2]
      ring
  have hs := testMaxwell_smul 1 (fun _ => 1) E (fun x i => -H x i)
    ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) hn
  convert hs using 1; ext x i; simp [FullChannelTEMatch.normalizedElectric, normalizedMagnetic, E, H]

/-- The actual compact-dielectric volume solution obeys Maxwell for every
    normalized transverse angular L² input whenever its physical volume block is invertible. -/
theorem normalized_material_maxwell (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) :
    TestMaxwell 1 (dielectric c)
      (MaterialField.total c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (FullChannelTEMatch.normalizedElectric F))
      (totalMagnetic c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (normalizedMagnetic F)) := by
  apply MaterialMaxwell.volume_solution_testMaxwell c 1 d.radius _ _ _ _ d.ballZero
    (FullChannelTEMatch.normalized_datum_actual c d F hF)
  · exact congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 =>
      L (FullChannelTEMatch.normalizedDatum c d F hF))
      (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c 1 d.radius) hu)
  · intro i
    exact (continuous_const.mul (FullChannelHerglotz.electric_continuous (-1) F hF i)).locallyIntegrable
  · intro i
    exact (continuous_const.mul (FullChannelMagnetic.magnetic_continuous (-1) F i)).locallyIntegrable
  · exact normalized_incident_maxwell F hF

end OQ14.FullChannelMaterialMaxwell
#print axioms OQ14.FullChannelMaterialMaxwell.normalized_incident_maxwell
#print axioms OQ14.FullChannelMaterialMaxwell.normalized_material_maxwell

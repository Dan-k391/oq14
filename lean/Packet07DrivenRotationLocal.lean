import Packet07DrivenAxialMaxwell
import Packet06CyclicRotationMaxwell

/-! Proper isometries preserve the local integrability required by Maxwell tests. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenRotationLocal
open MeasureTheory Set Maxwell ModalAxialRotation Packet07DrivenAxialPair

theorem isometry_comp (L : Space ≃ₗᵢ[ℝ] Space) (f : Space → ℂ) (hf : LocallyIntegrable f) :
    LocallyIntegrable (fun x => f (L x)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact ((L.measurePreserving.integrableOn_image L.toHomeomorph.measurableEmbedding).mp
    (hf.integrableOn_isCompact (hK.image L.continuous)))

theorem axial_field_local (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) :
    ∀ i, LocallyIntegrable (fun x => rotateField θ F x i) := by
  have h0 := isometry_comp (rotation (-θ)) (fun x => F x 0) (hF 0)
  have h1 := isometry_comp (rotation (-θ)) (fun x => F x 1) (hF 1)
  have h2 := isometry_comp (rotation (-θ)) (fun x => F x 2) (hF 2)
  intro i
  fin_cases i
  · simpa only [rotateField,vector,Matrix.cons_val_zero,smul_eq_mul] using (h0.smul (Real.cos θ : ℂ)).sub (h1.smul (Real.sin θ : ℂ))
  · simpa only [rotateField,vector,Matrix.cons_val_one,smul_eq_mul] using (h0.smul (Real.sin θ : ℂ)).add (h1.smul (Real.cos θ : ℂ))
  · exact h2

theorem cyclic_field_local (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) :
    ∀ i, LocallyIntegrable (fun x => Packet06CyclicRotationMaxwell.rotateField F x i) := by
  intro i
  exact isometry_comp Packet06CyclicRotation.rotation.symm (fun x => F x (WeakCurl.previous i)) (hF _)
end OQ14.Packet07DrivenRotationLocal
#print axioms OQ14.Packet07DrivenRotationLocal.isometry_comp
#print axioms OQ14.Packet07DrivenRotationLocal.axial_field_local
#print axioms OQ14.Packet07DrivenRotationLocal.cyclic_field_local

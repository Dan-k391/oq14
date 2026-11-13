import Packet07DrivenAxialPair
import Packet06AxialPhaseField

/-! Actual one-sided representatives of any driven field under an axial rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenAxialPhaseAE
open MeasureTheory Set Maxwell ModalAxialRotation Packet06AxialPhaseField Packet07DrivenAxialPair

theorem component_image_ae (θ : ℝ) (E : Field) (V : Set Space) (hV : MeasurableSet V)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ j, (fun x => E x j) =ᵐ[volume.restrict V] reps j) (i : Fin 3) :
    (fun y => rotateField θ E y i) =ᵐ[volume.restrict ((rotation θ) '' V)] transport θ reps i := by
  have hset : MeasurableSet ((rotation θ) '' V) := by
    change MeasurableSet ((rotation θ).toEquiv '' V)
    rw [(rotation θ).toEquiv.image_eq_preimage]
    exact hV.preimage (rotation θ).symm.continuous.measurable
  have hr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
    (ae_all_iff.mpr (fun j => (ae_restrict_iff' hV).mp (hreps j)))
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hr] with y hr hy
  have hyV : rotation (-θ) y ∈ V := by
    obtain ⟨x,hx,rfl⟩ := hy
    simpa [rotation,spatial_inverse] using hx
  change vector θ (E (rotation (-θ) y)) i = ∑ j : Fin 3, matrix θ i j * reps j (rotation (-θ) y)
  rw [← matrix_vector]
  exact Finset.sum_congr rfl (fun j _ => by rw [hr j hyV])

end OQ14.Packet07DrivenAxialPhaseAE
#print axioms OQ14.Packet07DrivenAxialPhaseAE.component_image_ae

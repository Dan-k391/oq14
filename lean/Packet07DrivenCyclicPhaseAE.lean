import Packet06CyclicTraceGeneral
import Packet06CyclicRotationMaxwell

/-! Actual driven phase representatives under proper cyclic rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenCyclicPhaseAE
open MeasureTheory Set Maxwell Packet06CyclicRotation Packet06CyclicRotationMaxwell
  Packet06PlacementHomeomorph Packet06PlacedPhaseField

theorem component_image_ae (E : Field) (V : Set Space) (hV : MeasurableSet V)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ j, (fun x => E x j) =ᵐ[volume.restrict V] reps j) (i : Fin 3) :
    (fun y => rotateField E y i) =ᵐ[volume.restrict (placement 1 (by norm_num) 0 '' V)]
      transport 1 (by norm_num) 0 reps i := by
  let h := placement 1 (by norm_num) 0
  have hset : MeasurableSet (h '' V) := by
    change MeasurableSet (h.toEquiv '' V)
    rw [h.toEquiv.image_eq_preimage]
    exact hV.preimage h.symm.continuous.measurable
  have hr := rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    ((ae_restrict_iff' hV).mp (hreps (WeakCurl.previous i)))
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hr] with y hr hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hback : unrotate (h x)=x := by
    simp [h,placement,Packet06PhysicalPlacement.point,unrotate_rotate]
  have hh := hr (by simpa only [show rotation.symm (h x)=x from hback] using hx)
  change E (unrotate (h x)) (WeakCurl.previous i) = reps (WeakCurl.previous i) (unrotate (h x)) at hh
  rw [hback] at hh
  simpa [rotateField,transport,scale,h,placement,Packet06PhysicalPlacement.point,unrotate_rotate] using hh

end OQ14.Packet07DrivenCyclicPhaseAE
#print axioms OQ14.Packet07DrivenCyclicPhaseAE.component_image_ae

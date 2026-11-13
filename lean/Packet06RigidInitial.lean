import Packet06ModalRetainedHost
import Packet06RigidFrameGeometry
import Packet06RigidStateOutgoing

/-! The unconditional coordinate device supplies every local positivity and
actual-collar hypothesis of the composable rigid-motion state. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidInitial
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedExistence
  Packet06ModalRetainedHost Packet06RigidHotspotState Packet06RigidCollar

 def initial {N : ℕ} (d : Device N) (K target Q ρ M : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2)))
    (hv : Valid d K target Q ρ M P) (hr : Retained d) : State N d.frequency d.radius M d.collarBound := by
  refine ⟨d.material,d.unknown,d.supportRadius,supportRadius_nonneg d,hv.material_support,hv.kernel,hv.normalization,
    d.innerBody,{x : Maxwell.Space | x 2=0},d.center,hv.inner_open,?_,?_,?_⟩
  · intro i
    exact (observation_in_host d hr i).trans (host_enclosed d)
  · intro i x hx
    exact (host_positive d K target Q ρ M P hv x (observation_in_host d hr i hx)).ne'
  · intro i
    exact Packet06AxialHotspotStart.coordinate_hotspot d.material d.frequency d.unknown d.innerBody
      (d.center i) d.radius M d.collarBound (hv.hotspots i)

theorem initial_collars {N : ℕ} (d : Device N) (K target Q ρ M : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) (hv : Valid d K target Q ρ M P) (hr : Retained d) :
    HasCollars (initial d K target Q ρ M P hv hr) d.collar := by
  intro i
  refine ⟨hv.collar_open i,(hr.collar_in_host i).trans (host_enclosed d),?_,hv.collar_contains_sphere i,hv.collar_traces i⟩
  intro x hx
  exact (host_positive d K target Q ρ M P hv x (hr.collar_in_host i hx)).ne'

end OQ14.Packet06RigidInitial
#print axioms OQ14.Packet06RigidInitial.initial
#print axioms OQ14.Packet06RigidInitial.initial_collars

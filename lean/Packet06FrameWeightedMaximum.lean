import Packet06RigidWeightedStep

/-! An actual attained weighted maximum and its exact value survive the
entire Euler-plus-translation frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06FrameWeightedMaximum
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06RigidHotspotState Packet06RigidWeightedMaximum Packet06PhaseWeightedMaximum Packet06RigidWeightedStep
abbrev Space := Maxwell.Space

def HasValue {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) (i : Fin N) (n η W : ℝ) : Prop :=
  ∃ (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space),
    HasWeightedMaximum d.material z d.unknown d.body (closedBall (d.center i) r) n η inside outside b x ∧
    W = phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2

theorem axial_value {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B)
    (i : Fin N) (n η W : ℝ) (h : HasValue d i n η W) : HasValue (axial θ d) i n η W := by
  obtain ⟨inside,outside,b,x,hm,hW⟩ := h
  have h := axial_step θ d i n η inside outside b x hm
  exact ⟨_,_,b,_,h.1,hW.trans h.2.symm⟩

theorem affine_value {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B)
    (i : Fin N) (n η W : ℝ) (h : HasValue d i n η W) : HasValue (affine a d) i n η W := by
  obtain ⟨inside,outside,b,x,hm,hW⟩ := h
  have h := affine_step a d i n η inside outside b x hm
  exact ⟨_,_,b,_,h.1,hW.trans h.2.symm⟩

theorem cyclic_value {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B)
    (i : Fin N) (n η W : ℝ) (h : HasValue d i n η W) : HasValue (cyclic d) i n η W := by
  obtain ⟨inside,outside,b,x,hm,hW⟩ := h
  have h := cyclic_step d i n η inside outside b x hm
  exact ⟨_,_,b,_,h.1,hW.trans h.2.symm⟩

theorem full_frame_value {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space) (d : State N z r M B)
    (i : Fin N) (n η W : ℝ) (h : HasValue d i n η W) :
    HasValue (Packet06RigidHotspotFrame.transform θ φ a d) i n η W := by
  unfold Packet06RigidHotspotFrame.transform
  apply affine_value
  apply cyclic_value
  apply cyclic_value
  apply axial_value
  apply cyclic_value
  apply cyclic_value
  apply axial_value
  exact cyclic_value d i n η W h
end OQ14.Packet06FrameWeightedMaximum
#print axioms OQ14.Packet06FrameWeightedMaximum.axial_value
#print axioms OQ14.Packet06FrameWeightedMaximum.affine_value
#print axioms OQ14.Packet06FrameWeightedMaximum.cyclic_value
#print axioms OQ14.Packet06FrameWeightedMaximum.full_frame_value

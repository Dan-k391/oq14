import Packet06NeighborhoodWeightedAffine
import Packet07DrivenRigidHotspot

/-! Full arbitrary frame transports one and the same neighborhood-certified weighted maximum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet06NeighborhoodWeightedFrame
open Set Metric Maxwell ModalAxialRotation Packet06RigidHotspotState Packet06NeighborhoodWeighted
  Packet06NeighborhoodWeightedAffine Packet06PhaseWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph
abbrev Space := Maxwell.Space

def sets (θ φ : ℝ) (a : Space) (K : Set Space) : Set Space :=
  (placement 1 (by norm_num) a) '' ((placement 1 (by norm_num) 0) '' ((placement 1 (by norm_num) 0) ''
    ((rotation θ) '' ((placement 1 (by norm_num) 0) '' ((placement 1 (by norm_num) 0) ''
      ((rotation φ) '' ((placement 1 (by norm_num) 0) '' K)))))))

def branches (θ φ : ℝ) (a : Space) (f : Fin 3 → Space → ℂ) : Fin 3 → Space → ℂ :=
  Packet06PlacedPhaseField.transport 1 (by norm_num) a
    (Packet06PlacedPhaseField.transport 1 (by norm_num) 0
      (Packet06PlacedPhaseField.transport 1 (by norm_num) 0
        (Packet06AxialPhaseField.transport θ
          (Packet06PlacedPhaseField.transport 1 (by norm_num) 0
            (Packet06PlacedPhaseField.transport 1 (by norm_num) 0
              (Packet06AxialPhaseField.transport φ (Packet06PlacedPhaseField.transport 1 (by norm_num) 0 f)))))))

theorem frame {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space) (d : State N z r M B)
    (i : Fin N) (K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (h : Certificate d i K n η inside outside b x) :
    Certificate (Packet06RigidHotspotFrame.transform θ φ a d) i (sets θ φ a K) n η
      (branches θ φ a inside) (branches θ φ a outside) b (Packet07DrivenRigidHotspot.placement θ φ a x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (branches θ φ a inside)
      (branches θ φ a outside) b) (Packet07DrivenRigidHotspot.placement θ φ a x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  let h0 := placement 1 (by norm_num) 0
  let hA := placement 1 (by norm_num) a
  have h1 := Packet06NeighborhoodWeightedAffine.cyclic d i K n η inside outside b x h
  have h2 := Packet06NeighborhoodWeighted.axial φ (cyclic d) i _ n η _ _ b _ h1.1
  have h3 := Packet06NeighborhoodWeightedAffine.cyclic (axial φ (cyclic d)) i _ n η _ _ b _ h2.1
  have h4 := Packet06NeighborhoodWeightedAffine.cyclic (cyclic (axial φ (cyclic d))) i _ n η _ _ b _ h3.1
  have h5 := Packet06NeighborhoodWeighted.axial θ (cyclic (cyclic (axial φ (cyclic d)))) i _ n η _ _ b _ h4.1
  have h6 := Packet06NeighborhoodWeightedAffine.cyclic (axial θ (cyclic (cyclic (axial φ (cyclic d))))) i _ n η _ _ b _ h5.1
  have h7 := Packet06NeighborhoodWeightedAffine.cyclic (cyclic (axial θ (cyclic (cyclic (axial φ (cyclic d)))))) i _ n η _ _ b _ h6.1
  have h8 := Packet06NeighborhoodWeightedAffine.affine a (cyclic (cyclic (axial θ (cyclic (cyclic (axial φ (cyclic d))))))) i _ n η _ _ b _ h7.1
  have hp : hA (h0 (h0 (rotation θ (h0 (h0 (rotation φ (h0 x))))))) = Packet07DrivenRigidHotspot.placement θ φ a x := by
    change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
      (Packet06PhysicalPlacement.point 1 0 (rotation θ (Packet06PhysicalPlacement.point 1 0
        (Packet06PhysicalPlacement.point 1 0 (rotation φ (Packet06PhysicalPlacement.point 1 0 x))))))) = _
    simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,
      Packet06RigidHotspotFrame.cyclic_thrice,Packet06RigidHotspotFrame.twice_rotate]
    rw [Packet06CyclicRotation.rotate_unrotate]
    rfl
  dsimp only at h8
  dsimp only [h0,hA] at hp
  rw [hp] at h8
  refine ⟨h8.1,?_⟩
  exact h8.2.trans (h7.2.trans (h6.2.trans (h5.2.trans (h4.2.trans (h3.2.trans (h2.2.trans h1.2))))))

theorem sets_eq_image (θ φ : ℝ) (a : Space) (K : Set Space) :
    sets θ φ a K = Packet07DrivenRigidHotspot.placement θ φ a '' K := by
  simp only [sets,Set.image_image]
  have he : (fun x : Space => (placement 1 (by norm_num) a)
      ((placement 1 (by norm_num) 0) ((placement 1 (by norm_num) 0)
        (rotation θ ((placement 1 (by norm_num) 0) ((placement 1 (by norm_num) 0)
          (rotation φ ((placement 1 (by norm_num) 0) x)))))))) = Packet07DrivenRigidHotspot.placement θ φ a := by
    funext x
    change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
    (Packet06PhysicalPlacement.point 1 0 (rotation θ (Packet06PhysicalPlacement.point 1 0
      (Packet06PhysicalPlacement.point 1 0 (rotation φ (Packet06PhysicalPlacement.point 1 0 x))))))) = _
    simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,
      Packet06RigidHotspotFrame.cyclic_thrice,Packet06RigidHotspotFrame.twice_rotate]
    rw [Packet06CyclicRotation.rotate_unrotate]
    rfl
  rw [he]
end OQ14.Packet06NeighborhoodWeightedFrame
#print axioms OQ14.Packet06NeighborhoodWeightedFrame.frame
#print axioms OQ14.Packet06NeighborhoodWeightedFrame.sets_eq_image

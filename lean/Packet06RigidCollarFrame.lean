import Packet06RigidCollar
import Packet06RigidHotspotFrame

/-! Fixed one-sided collars follow the exact Euler-plus-translation chain. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidCollarFrame
open Set Maxwell Packet06RigidHotspotState Packet06RigidCollar Packet06PlacementHomeomorph
  ModalAxialRotation
abbrev Space := Maxwell.Space

def transformCollars {N : ℕ} (θ φ : ℝ) (a : Space) (A : Fin N → Set Space) : Fin N → Set Space :=
  fun i => (placement 1 (by norm_num) a) '' ((placement 1 (by norm_num) 0) ''
    ((placement 1 (by norm_num) 0) '' ((rotation θ) '' ((placement 1 (by norm_num) 0) ''
      ((placement 1 (by norm_num) 0) '' ((rotation φ) '' ((placement 1 (by norm_num) 0) '' A i)))))))

theorem transform_collars {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (A : Fin N → Set Space) (hA : HasCollars d A) :
    HasCollars (Packet06RigidHotspotFrame.transform θ φ a d) (transformCollars θ φ a A) := by
  let c1 := cyclic d
  let a1 := axial φ c1
  let c2 := cyclic a1
  let c3 := cyclic c2
  let a2 := axial θ c3
  let c4 := cyclic a2
  let c5 := cyclic c4
  have h1 := cyclic_collar d A hA
  have h2 := axial_collar φ c1 _ h1
  have h3 := cyclic_collar a1 _ h2
  have h4 := cyclic_collar c2 _ h3
  have h5 := axial_collar θ c3 _ h4
  have h6 := cyclic_collar a2 _ h5
  have h7 := cyclic_collar c4 _ h6
  exact affine_collar a c5 _ h7

end OQ14.Packet06RigidCollarFrame
#print axioms OQ14.Packet06RigidCollarFrame.transform_collars

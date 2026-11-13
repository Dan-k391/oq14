import Packet06ConeSymmetry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SphereSymmetry
open Packet06MaterialSymmetry

theorem sphere_axial (n : ℝ) (hn : 1 < n) : Axial (ModalWeightedMode.coefficient n hn) := by
  intro θ x
  exact ModalAxialRotation.material_invariant n hn θ x

theorem sphere_meridional (n : ℝ) (hn : 1 < n) : Meridional (ModalWeightedMode.coefficient n hn) := by
  intro x
  exact ModalMeridionalReflection.sphere_symmetric n hn x
#print axioms OQ14.Packet06SphereSymmetry.sphere_axial
#print axioms OQ14.Packet06SphereSymmetry.sphere_meridional
end OQ14.Packet06SphereSymmetry

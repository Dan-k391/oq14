import Packet05GraphPiolaH2
import Packet05DirectionalWeightDerivative
import Packet05WeakFourier

/-! The binary dielectric times H² forcing retains exactly the tangential
weak derivatives needed by the scalar transmission iteration. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05BinaryForcingTangential
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05WeakFourier OQ14.Packet05DirectionalWeightDerivative
  OQ14.Packet05GraphPiolaH2

theorem binary_h2_tangential (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar)
    (hu : CompactRepresentative u) (h2 : HasH2 u) (i t : Fin 3)
    (hi : i ≠ 2) (ht : t ≠ 2) :
    ∃ Di Dt Dit : L2Scalar,
      HasWeakPartial (mulWeight d hd u) Di i ∧
      HasWeakPartial (mulWeight d hd u) Dt t ∧
      HasWeakPartial Di Dit t := by
  obtain ⟨G,H,hG,hH⟩ := h2
  have hGi : CompactRepresentative (G i) := weak_partial_compact hu i (hG i)
  exact ⟨mulWeight d hd (G i), mulWeight d hd (G t), mulWeight d hd (H i t),
    directional_weighted_tangential_partial d hd u (G i) hu i hi (hG i),
    directional_weighted_tangential_partial d hd u (G t) hu t ht (hG t),
    directional_weighted_tangential_partial d hd (G i) (H i t) hGi t ht (hH i t)⟩

end OQ14.Packet05BinaryForcingTangential
#print axioms OQ14.Packet05BinaryForcingTangential.binary_h2_tangential

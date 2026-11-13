import Packet05WeightTangentialDerivative
import Packet05DirectionalQuotient

/-! Binary-weight commutation needs only the selected tangential weak
partial, not a full H¹ field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05DirectionalWeightDerivative
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05LocalDerivative OQ14.MaxwellDifferenceQuotient OQ14.Packet05DirectionalQuotient

theorem directional_weighted_tangential_partial (d : ℝ) (hd : 0 ≤ d)
    (u Du : L2Scalar) (hu : CompactRepresentative u) (i : Fin 3) (hi : i ≠ 2)
    (hU : HasWeakPartial u Du i) : HasWeakPartial (mulWeight d hd u) (mulWeight d hd Du) i := by
  have hq : ∀ h : ℝ, h ≠ 0 → |h| < 1 → ‖quotient u i h‖ ≤ ‖Du‖ := by
    intro h hh _
    exact directional_quotient_bound u Du hu i hU h hh
  obtain ⟨v,hv,_⟩ := weighted_weakPartial_of_bounded_quotients d hd u i hi ‖Du‖ 1 (norm_nonneg _) (by norm_num) hq
  have he := weighted_partial_eq d hd u Du v i hU hv
  rw [he] at hv
  exact hv

end OQ14.Packet05DirectionalWeightDerivative
#print axioms OQ14.Packet05DirectionalWeightDerivative.directional_weighted_tangential_partial

import Packet05LocalDerivative
import MaxwellDifferenceQuotient

/-! A tangential weak derivative commutes with the genuine binary jump.
Existence is proved by bounded quotients, and the derivative is identified
on both open phases; the interface itself has zero volume. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05WeightTangentialDerivative
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05LocalDerivative OQ14.MaxwellDifferenceQuotient

theorem weighted_tangential_weak_partial (d : ℝ) (hd : 0 ≤ d)
    (u : L2Scalar) (U : Fin 3 → L2Scalar) (hu : CompactRepresentative u)
    (hU : ∀ i, HasWeakPartial u (U i) i) (i : Fin 3) (hi : i ≠ 2) :
    HasWeakPartial (mulWeight d hd u) (mulWeight d hd (U i)) i := by
  let B : ℝ := ∑ j : Fin 3, ‖U j‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hq : ∀ h : ℝ, h ≠ 0 → |h| < 1 → ‖quotient u i h‖ ≤ B := by
    intro h hh _
    exact quotient_bound hu hU i h hh
  obtain ⟨v,hv,_⟩ := weighted_weakPartial_of_bounded_quotients d hd u i hi B 1 hB (by norm_num) hq
  have he := weighted_partial_eq d hd u (U i) v i (hU i) hv
  rw [he] at hv
  exact hv

end OQ14.Packet05WeightTangentialDerivative
#print axioms OQ14.Packet05WeightTangentialDerivative.weighted_tangential_weak_partial

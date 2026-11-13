import Packet05ActualSecondOriginalBound
import Packet05LocalSecondTangential
import Packet05LocalDerivative

/-! Align the two nested second-iteration arrays without losing norm bounds. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativeNestedAlignment
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05LocalSecondTangential
  OQ14.Packet05LocalDerivative

theorem align_nested_derivatives (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (τ κ ζ : RealTest univ) (hτ : ∀ x ∈ V, τ.function x = 1)
    (hκW : ∀ x ∈ W, κ.function x = 1) (hζW : ∀ x ∈ W, ζ.function x = 1)
    (C : L2Vector) (i : Fin 3)
    (D0 D1 H0 H1 : L2Vector)
    (hD0 : ∀ j, HasWeakPartial (cutScalar τ (C j)) (D0 j) i)
    (hD1 : ∀ j, HasWeakPartial (cutScalar τ (C j)) (D1 j) i)
    (hH0 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D0 j)) (H0 j) 0)
    (hH1 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D1 j)) (H1 j) 1)
    (A B0 B1 : ℝ) (hA : (∑ j : Fin 3, ‖D0 j‖) ≤ A)
    (hB0 : ∀ j, ‖H0 j‖ ≤ B0) (hB1 : ∀ j, ‖H1 j‖ ≤ B1) :
    (∀ j, HasPartialOn W (C j) (D0 j) i) ∧
    (∀ j, HasPartialOn W (D0 j) (H0 j) 0) ∧
    (∀ j, HasPartialOn W (D0 j) (H1 j) 1) ∧
    (∑ j : Fin 3, ‖D0 j‖) ≤ A ∧ (∀ j, ‖H0 j‖ ≤ B0) ∧ (∀ j, ‖H1 j‖ ≤ B1) := by
  have heq : D1 = D0 := by
    funext j
    exact weak_partial_unique (cutScalar τ (C j)) (D1 j) (D0 j) i (hD1 j) (hD0 j)
  subst D1
  refine ⟨?_,?_,?_,hA,hB0,hB1⟩
  · intro j
    apply OQ14.Packet05RegionalPartial.cutoff_partial_on W τ.complexTest.toTest (C j) (D0 j) i
    · intro x hx
      simp [RealTest.complexTest,hτ x (hWV hx)]
    · exact hD0 j
  · intro j
    exact nested_to_local_second W hW κ ζ hκW hζW (C i) D0 j 0 (H0 j) (hH0 j)
  · intro j
    exact nested_to_local_second W hW κ ζ hκW hζW (C i) D0 j 1 (H1 j) (hH1 j)

end OQ14.Packet05QuantitativeNestedAlignment
#print axioms OQ14.Packet05QuantitativeNestedAlignment.align_nested_derivatives

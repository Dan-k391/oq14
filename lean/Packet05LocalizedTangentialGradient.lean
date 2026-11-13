import Packet05TangentialGradientArrays
import Packet05RegionalScalarLocalization

/-! The actual localized tangential scalar gradient has explicit first
weak derivatives, including the cutoff commutator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalizedTangentialGradient
open Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05ScalarCutoffTransfer Packet05LocalPartialProduct
  Packet05ScalarLocalTangentialH2 Packet05CurlSourceH1 Packet05DifferentiatedSourceBounds
  Packet05RegionalScalarLocalization

theorem localized_gradient_derivatives (V : Set Space) (hV : IsOpen V)
    (u : L2Scalar) (C : L2Vector) (hC : ∀ j, HasWeakPartial u (C j) j)
    (i : Fin 3) (D : L2Vector) (hD : ∀ j, HasPartialOn V (C j) (D j) i)
    (κ : RealTest univ) (hκV : tsupport κ.function ⊆ V) (a b : ℝ)
    (ha : ∀ x, ‖κ.complexTest.function x‖ ≤ a)
    (hb : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ b) :
    (∀ j, HasWeakPartial (cutScalar κ (C i)) (localizedGradient κ (C i) D j) j) ∧
    (∀ j, ‖localizedGradient κ (C i) D j‖ ≤ a*‖D j‖+b*‖C i‖) := by
  have hκV' : tsupport κ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hκV
  constructor
  · intro j
    have hmix : HasPartialOn V (C i) (D j) j :=
      mixed_partial_on_commute V hV u (C j) (C i) (D j) j i
        (global_partial_on V u (C j) j (hC j)) (global_partial_on V u (C i) i (hC i)) (hD j)
    exact local_cutoff_weak_partial V κ.complexTest.toTest hκV' (C i) (D j) j hmix
  · intro j
    exact cutoff_product_norm κ.complexTest.toTest (C i) (D j) j a b ha (hb j)

end OQ14.Packet05LocalizedTangentialGradient
#print axioms OQ14.Packet05LocalizedTangentialGradient.localized_gradient_derivatives

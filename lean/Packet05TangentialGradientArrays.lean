import Packet05TangentialPlateauBound
import Packet05DifferentiatedSourceBounds
import Packet05ScalarLocalTangentialH2

/-! Explicit mixed derivative arrays for a localized tangential gradient,
with their cutoff norms retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TangentialGradientArrays
open Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05ScalarCutoffTransfer Packet05LocalPartialProduct
  Packet05ScalarLocalTangentialH2 Packet05CurlSourceH1 Packet05DifferentiatedSourceBounds

def mixedArray (θ : Test) (D : Fin 3 → L2Scalar) (H : Fin 3 → Fin 3 → L2Scalar)
    (i j : Fin 3) : L2Scalar := cutoffProductDerivative θ (D i) (H i j) j

theorem tangential_gradient_arrays (W : Set Space) (hW : IsOpen W)
    (u : L2Scalar) (D : Fin 3 → L2Scalar) (hD : ∀ j, HasWeakPartial u (D j) j)
    (ζ : RealTest univ) (hζ : ∀ x ∈ W, ζ.function x = 1)
    (θ : Test) (hθW : tsupport θ.function ⊆ W)
    (H : Fin 3 → Fin 3 → L2Scalar)
    (hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (cutScalar ζ (D j)) (H i j) i)
    (a b : ℝ) (ha : ∀ x, ‖θ.function x‖ ≤ a) (hb : ∀ i x, ‖dcoord θ.function x i‖ ≤ b) :
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 θ.function θ.regular.continuous θ.compact (D i)) (mixedArray θ D H i j) j) ∧
    (∀ i j, ‖mixedArray θ D H i j‖ ≤ a*‖H i j‖+b*‖D i‖) := by
  have hζc : ∀ x ∈ W, ζ.complexTest.function x = 1 := by
    intro x hx
    simp [RealTest.complexTest,hζ x hx]
  constructor
  · intro i hi j
    have hlocal : HasPartialOn W (D j) (H i j) i :=
      cutoff_partial_on W ζ.complexTest.toTest (D j) (H i j) i hζc (hH i hi j)
    have hmix : HasPartialOn W (D i) (H i j) j :=
      mixed_partial_on_commute W hW u (D j) (D i) (H i j) j i
        (global_partial_on W u (D j) j (hD j)) (global_partial_on W u (D i) i (hD i)) hlocal
    exact local_cutoff_weak_partial W θ hθW (D i) (H i j) j hmix
  · intro i j
    exact cutoff_product_norm θ (D i) (H i j) j a b ha (hb j)

end OQ14.Packet05TangentialGradientArrays
#print axioms OQ14.Packet05TangentialGradientArrays.tangential_gradient_arrays

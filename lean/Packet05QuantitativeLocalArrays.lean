import Packet05CutoffLocalSecond
import Packet05MixedCutoffSourceBounds

/-! Explicit global weak-derivative arrays and their norm bounds from the
actual regional tangential derivatives. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativeLocalArrays
open Set Maxwell WeakCurl WeakPoynting WeakGreen DivCurlCompact Packet05RegionalPartial
  Packet05CutoffLocalSecond Packet05CurlSourceH1 MaxwellCutoffCommutator
  Packet05DifferentiatedSourceBounds Packet05MixedCutoffSourceBounds

def first (χ : Test) (C : L2Vector) (D : Fin 3 → L2Vector) (i j : Fin 3) : L2Scalar :=
  cutoffProductDerivative χ (C j) (D i j) i

def second (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (C : L2Vector)
    (D : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector) (i t j : Fin 3) : L2Scalar :=
  cutoffProductDerivative χ (D i j) (H i t j) t +
    cutoffProductDerivative (derivativeCutoff χ hχ2 i) (C j) (D t j) t

theorem local_arrays (V : Set Space) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχV : tsupport χ.function ⊆ V) (C : L2Vector)
    (D : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector)
    (hD : ∀ i, i ≠ 2 → ∀ j, HasPartialOn V (C j) (D i j) i)
    (hH : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn V (D i j) (H i t j) t) :
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (C j)) (first χ C D i j) i) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial
      (first χ C D i j) (second χ hχ2 C D H i t j) t) := by
  constructor
  · intro i hi j
    exact (cutoff_local_second V χ hχ2 hχV (C j) (D i j) (D i j) (H i i j)
      i i (hD i hi j) (hD i hi j) (hH i hi i hi j)).1
  · intro i hi t ht j
    exact (cutoff_local_second V χ hχ2 hχV (C j) (D i j) (D t j) (H i t j)
      i t (hD i hi j) (hD t ht j) (hH i hi t ht j)).2

theorem first_norm (χ : Test) (C : L2Vector) (D : Fin 3 → L2Vector) (i j : Fin 3)
    (a b : ℝ) (ha : ∀ x, ‖χ.function x‖ ≤ a) (hb : ∀ t x, ‖dcoord χ.function x t‖ ≤ b) :
    ‖first χ C D i j‖ ≤ a*‖D i j‖+b*‖C j‖ :=
  cutoff_product_norm χ (C j) (D i j) i a b ha (hb i)

theorem second_norm (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (C : L2Vector)
    (D : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector) (i t j : Fin 3)
    (a b c : ℝ) (ha : ∀ x, ‖χ.function x‖ ≤ a) (hb : ∀ k x, ‖dcoord χ.function x k‖ ≤ b)
    (hc : ∀ k l x, ‖dcoord (derivativeCutoff χ hχ2 k).function x l‖ ≤ c) :
    ‖second χ hχ2 C D H i t j‖ ≤
      a*‖H i t j‖+b*‖D i j‖+b*‖D t j‖+c*‖C j‖ :=
  mixed_cutoff_product_norm χ hχ2 (C j) (D i j) (D t j) (H i t j) i t a b c ha hb (hc i t)

end OQ14.Packet05QuantitativeLocalArrays
#print axioms OQ14.Packet05QuantitativeLocalArrays.local_arrays
#print axioms OQ14.Packet05QuantitativeLocalArrays.first_norm
#print axioms OQ14.Packet05QuantitativeLocalArrays.second_norm

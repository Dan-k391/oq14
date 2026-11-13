import Packet05GraphH2Norm
import Packet05BoundedMultiplierH2

/-! Quantitative H² product rule for a fixed bounded C² multiplier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05MultiplierH2Norm
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05BoundedWeakMultiplier OQ14.Packet05LocalizedAnisotropic
  OQ14.Packet05GraphH2Norm

theorem bounded_multiplier_h2_norm (a : Space → ℂ) (ha : ContDiff ℝ 2 a)
    (hbound : MemLp a ⊤ volume)
    (hdi : ∀ i, MemLp (fun x => dcoord a x i) ⊤ volume)
    (hdd : ∀ i j, MemLp (fun x => dcoord (fun y => dcoord a y i) x j) ⊤ volume)
    (A B C : ℝ) (hA : ∀ x, ‖a x‖ ≤ A)
    (hB : ∀ i x, ‖dcoord a x i‖ ≤ B)
    (hC : ∀ i j x, ‖dcoord (fun y => dcoord a y i) x j‖ ≤ C)
    (u : L2Scalar) (G : L2Vector) (H : Fin 3 → L2Vector)
    (hG : ∀ i, HasWeakPartial u (G i) i) (hH : ∀ i j, HasWeakPartial (G i) (H i j) j) :
    ∃ D : L2Vector, ∃ K : Fin 3 → L2Vector,
      (∀ i, HasWeakPartial (boundedMultiply a hbound u) (D i) i) ∧
      (∀ i j, HasWeakPartial (D i) (K i j) j) ∧
      (∀ i, ‖D i‖ ≤ A*‖G i‖+B*‖u‖) ∧
      (∀ i j, ‖K i j‖ ≤ A*‖H i j‖ + B*(‖G i‖+‖G j‖) + C*‖u‖) := by
  let D (i : Fin 3) := boundedMultiply a hbound (G i) +
    boundedMultiply (fun x => dcoord a x i) (hdi i) u
  let K (i j : Fin 3) :=
    (boundedMultiply a hbound (H i j) + boundedMultiply (fun x => dcoord a x j) (hdi j) (G i)) +
    (boundedMultiply (fun x => dcoord a x i) (hdi i) (G j) +
      boundedMultiply (fun x => dcoord (fun y => dcoord a y i) x j) (hdd i j) u)
  refine ⟨D,K,?_,?_,?_,?_⟩
  · intro i
    exact bounded_multiplier_weak_partial a (ha.of_le (by norm_num)) hbound i (hdi i) u (G i) (hG i)
  · intro i j
    have hai : ContDiff ℝ 1 (fun x => dcoord a x i) := KernelSource.partial_contDiff ha i
    have h1 := bounded_multiplier_weak_partial a (ha.of_le (by norm_num)) hbound j (hdi j)
      (G i) (H i j) (hH i j)
    have h2 := bounded_multiplier_weak_partial (fun x => dcoord a x i) hai (hdi i) j (hdd i j)
      u (G j) (hG j)
    exact weak_partial_add _ _ _ _ j h1 h2
  · intro i
    have h1 := bounded_multiply_norm a hbound (G i) A hA
    have h2 := bounded_multiply_norm (fun x => dcoord a x i) (hdi i) u B (hB i)
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  · intro i j
    have h1 := bounded_multiply_norm a hbound (H i j) A hA
    have h2 := bounded_multiply_norm (fun x => dcoord a x j) (hdi j) (G i) B (hB j)
    have h3 := bounded_multiply_norm (fun x => dcoord a x i) (hdi i) (G j) B (hB i)
    have h4 := bounded_multiply_norm (fun x => dcoord (fun y => dcoord a y i) x j) (hdd i j) u C (hC i j)
    have hn1 := norm_add_le (boundedMultiply a hbound (H i j)) (boundedMultiply (fun x => dcoord a x j) (hdi j) (G i))
    have hn2 := norm_add_le (boundedMultiply (fun x => dcoord a x i) (hdi i) (G j)) (boundedMultiply (fun x => dcoord (fun y => dcoord a y i) x j) (hdd i j) u)
    change ‖_ + _‖ ≤ _
    exact (norm_add_le _ _).trans (by nlinarith)

end OQ14.Packet05MultiplierH2Norm
#print axioms OQ14.Packet05MultiplierH2Norm.bounded_multiplier_h2_norm

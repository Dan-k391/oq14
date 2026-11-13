import Packet05MetricSecondBound

/-! Common nonnegative value, first and second derivative bounds for a
finite smooth compact chart metric. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05MetricAllBounds
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact Packet05MatrixWeakDerivative

theorem matrix_all_bounds (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      (∀ j k x, ‖(A j k).function x‖ ≤ a) ∧
      (∀ j k i x, ‖dcoord (A j k).function x i‖ ≤ b) ∧
      ∀ j k i t x, ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ c := by
  have hex (j k : Fin 3) : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      (∀ x, ‖(A j k).function x‖ ≤ a) ∧ (∀ i x, ‖dcoord (A j k).function x i‖ ≤ b) ∧
      ∀ i t x, ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ c := by
    obtain ⟨a,b,c,ha,hb,hc,h0,h1,h2⟩ := Packet05CutoffSecondBound.derivative_bounds (A j k) (hA2 j k)
    exact ⟨a,b,c,ha,hb,hc,h0,h1,h2⟩
  choose a b c ha hb hc h0 h1 h2 using hex
  let A0 := ∑ j : Fin 3, ∑ k : Fin 3, a j k
  let B0 := ∑ j : Fin 3, ∑ k : Fin 3, b j k
  let C0 := ∑ j : Fin 3, ∑ k : Fin 3, c j k
  refine ⟨A0,B0,C0,Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => ha j k)),
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hb j k)),
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hc j k)),?_,?_,?_⟩
  · intro j k x
    exact (h0 j k x).trans ((Finset.single_le_sum (fun l _ => ha j l) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => ha l m)) (Finset.mem_univ j)))
  · intro j k i x
    exact (h1 j k i x).trans ((Finset.single_le_sum (fun l _ => hb j l) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => hb l m)) (Finset.mem_univ j)))
  · intro j k i t x
    exact (h2 j k i t x).trans ((Finset.single_le_sum (fun l _ => hc j l) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => hc l m)) (Finset.mem_univ j)))

end OQ14.Packet05MetricAllBounds
#print axioms OQ14.Packet05MetricAllBounds.matrix_all_bounds

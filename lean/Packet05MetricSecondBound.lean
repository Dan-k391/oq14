import Packet05CutoffSecondBound

/-! A finite C² chart metric has one uniform second-coordinate-derivative
bound, chosen independently of the electromagnetic field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05MetricSecondBound
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05MatrixWeakDerivative

theorem matrix_second_bound (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j k i t x,
      ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ C := by
  have hex (j k : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i t x,
      ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ C := by
    obtain ⟨a,b,c,ha,hb,hc,_,_,h⟩ := Packet05CutoffSecondBound.derivative_bounds (A j k) (hA2 j k)
    exact ⟨c,hc,fun i t x => h i t x⟩
  choose C hC using hex
  let D := ∑ j : Fin 3, ∑ k : Fin 3, C j k
  refine ⟨D,Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => (hC j k).1)),?_⟩
  intro j k i t x
  exact ((hC j k).2 i t x).trans
    ((Finset.single_le_sum (fun l _ => (hC j l).1) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => (hC l m).1)) (Finset.mem_univ j)))

end OQ14.Packet05MetricSecondBound
#print axioms OQ14.Packet05MetricSecondBound.matrix_second_bound

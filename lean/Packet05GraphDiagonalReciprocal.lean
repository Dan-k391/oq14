import Packet05CutoffReciprocal
import Packet05GraphChartMatrix

/-! The normal principal coefficient of a flattened graph is strictly positive,
so a compact reciprocal follows from the actual graph metric. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphDiagonalReciprocal
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.Packet05CutoffReciprocal
  OQ14.Packet05GraphChartMatrix

theorem graph_diagonal_ne_zero (a b : ℝ) :
    ((metric a b 2 2 : ℝ) : ℂ) ≠ 0 := by
  have h : 0 < 1 + a^2 + b^2 := by positivity
  simp only [metric, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.head_cons]
  exact_mod_cast ne_of_gt h

theorem graph_diagonal_reciprocal (V W : Set Space) (κ : Test)
    (A : Fin 3 → Fin 3 → Test) (a b : Space → ℝ)
    (hκV : tsupport κ.function ⊆ V) (hWV : W ⊆ V)
    (hmetric : ∀ x ∈ V, (A 2 2).function x = ((metric (a x) (b x) 2 2 : ℝ) : ℂ))
    (hκ : ∀ x ∈ W, κ.function x = 1) :
    ∃ r : Test, tsupport r.function ⊆ V ∧
      ∀ x ∈ W, r.function x * (A 2 2).function x = 1 := by
  have hne : ∀ x ∈ V, (A 2 2).function x ≠ 0 := by
    intro x hx
    rw [hmetric x hx]
    exact graph_diagonal_ne_zero (a x) (b x)
  have hs : ∀ x ∈ tsupport κ.function, (A 2 2).function x ≠ 0 :=
    fun x hx => hne x (hκV hx)
  refine ⟨reciprocalTest κ (A 2 2) hs, ?_, ?_⟩
  · exact (reciprocalTest_support κ (A 2 2) hs).trans hκV
  · exact reciprocalTest_identity κ (A 2 2) hs W hκ (fun x hx => hne x (hWV hx))

end OQ14.Packet05GraphDiagonalReciprocal
#print axioms OQ14.Packet05GraphDiagonalReciprocal.graph_diagonal_ne_zero
#print axioms OQ14.Packet05GraphDiagonalReciprocal.graph_diagonal_reciprocal

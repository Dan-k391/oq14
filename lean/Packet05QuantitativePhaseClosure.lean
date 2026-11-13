import Packet05QuantitativePhysicalBranches

/-! Continuous physical branch bounds extend to each material-side closure. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativePhaseClosure
open Set Maxwell
open scoped Topology

theorem continuous_bound_on_closure (U : Set Space) (f : Space → ℂ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ x ∈ U, ‖f x‖ ≤ B) :
    ∀ x ∈ closure U, ‖f x‖ ≤ B := by
  have hc : IsClosed {x : Space | ‖f x‖ ≤ B} := isClosed_le hf.norm continuous_const
  exact closure_minimal hB hc

theorem bounded_phase_closure (U : Set Space) (reps : Fin 3 → Space → ℂ)
    (hcont : ∀ j, Continuous (reps j)) (B : ℝ) (hB : ∀ j x, x ∈ U → ‖reps j x‖ ≤ B) :
    ∀ j x, x ∈ closure U → ‖reps j x‖ ≤ B := by
  intro j
  exact continuous_bound_on_closure U (reps j) (hcont j) B (hB j)

end OQ14.Packet05QuantitativePhaseClosure
#print axioms OQ14.Packet05QuantitativePhaseClosure.continuous_bound_on_closure
#print axioms OQ14.Packet05QuantitativePhaseClosure.bounded_phase_closure

import Packet05NestedCutoffSupport

/-! Five nested smooth cutoff triples chosen once inside a fixed open chart.
They supply the regional bootstrap, two scalar iterations, and final
normal-flux and tangential representative plateaus. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05FiveNestedCutoffs
open Set Metric Maxwell Packet05NestedChartCutoffs Packet05NestedCutoffSupport

structure Data (Ω : Set Space) (p : Space) where
  q0 : Packet05NestedChartCutoffs.Data Ω p
  q1 : Packet05NestedChartCutoffs.Data (ball p (2*q0.r)) p
  q2 : Packet05NestedChartCutoffs.Data (ball p (2*q1.r)) p
  q3 : Packet05NestedChartCutoffs.Data (ball p (2*q2.r)) p
  q4 : Packet05NestedChartCutoffs.Data (ball p (4*q3.r)) p

theorem exists_five (Ω : Set Space) (hΩ : IsOpen Ω) (p : Space) (hp : p ∈ Ω) : Nonempty (Data Ω p) := by
  obtain ⟨q0⟩ := exists_nested Ω hΩ p hp
  obtain ⟨q1⟩ := exists_nested (ball p (2*q0.r)) isOpen_ball p (mem_ball_self (by linarith [q0.positive]))
  obtain ⟨q2⟩ := exists_nested (ball p (2*q1.r)) isOpen_ball p (mem_ball_self (by linarith [q1.positive]))
  obtain ⟨q3⟩ := exists_nested (ball p (2*q2.r)) isOpen_ball p (mem_ball_self (by linarith [q2.positive]))
  obtain ⟨q4⟩ := exists_nested (ball p (4*q3.r)) isOpen_ball p (mem_ball_self (by linarith [q3.positive]))
  exact ⟨⟨q0,q1,q2,q3,q4⟩⟩

theorem plateaus {Ω : Set Space} {p : Space} (q : Data Ω p) :
    ball p (8*q.q1.r) ⊆ ball p (2*q.q0.r) ∧
    ball p (8*q.q2.r) ⊆ ball p (2*q.q1.r) ∧
    ball p (8*q.q3.r) ⊆ ball p (2*q.q2.r) ∧
    ball p (8*q.q4.r) ⊆ ball p (4*q.q3.r) :=
  ⟨ball8_subset q.q1,ball8_subset q.q2,ball8_subset q.q3,ball8_subset q.q4⟩

end OQ14.Packet05FiveNestedCutoffs
#print axioms OQ14.Packet05FiveNestedCutoffs.exists_five
#print axioms OQ14.Packet05FiveNestedCutoffs.plateaus

import Packet05QuantitativePhaseClosure

/-! Local phase estimates extend exactly to the domain used by finite-cover
branch gluing, including interface points. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhaseCoverLocalBound
open Set Maxwell Packet05QuantitativePhaseClosure
open scoped Topology

theorem local_phase_bound (U O : Set Space) (hO : IsOpen O)
    (f : Space → ℂ) (hf : Continuous f) (B : ℝ)
    (h : ∀ x ∈ U ∩ O, ‖f x‖ ≤ B) :
    ∀ x ∈ closure U ∩ O, ‖f x‖ ≤ B := by
  exact fun x hx => continuous_bound_on_closure (U ∩ O) f hf B h x (hO.closure_inter hx)

theorem family_phase_bound {A : Type*} (U O : Set Space) (hO : IsOpen O)
    (f : A → Space → ℂ) (hf : ∀ a, Continuous (f a)) (B : ℝ) (data : A → ℝ)
    (h : ∀ a x, x ∈ U ∩ O → ‖f a x‖ ≤ B*data a) :
    ∀ a x, x ∈ closure U ∩ O → ‖f a x‖ ≤ B*data a := by
  intro a
  exact local_phase_bound U O hO (f a) (hf a) (B*data a) (h a)

end OQ14.Packet05PhaseCoverLocalBound
#print axioms OQ14.Packet05PhaseCoverLocalBound.local_phase_bound
#print axioms OQ14.Packet05PhaseCoverLocalBound.family_phase_bound

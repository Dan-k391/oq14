import Packet05ActualScalarTangentialContinuity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual a.e. rotational symmetry propagates to a continuous phase
representative and its boundary closure. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhaseSymmetry
open MeasureTheory Set OQ14.Maxwell

theorem continuous_phase_symmetry (V : Set Space) (hV : IsOpen V)
    (f : Space → ℝ) (hf : Continuous f) (T : Space → Space) (hT : Continuous T)
    (h : f ∘ T =ᵐ[volume.restrict V] f) :
    ∀ x ∈ closure V, f (T x) = f x := by
  have he : EqOn (f ∘ T) f V :=
    Measure.eqOn_open_of_ae_eq h hV (hf.comp hT).continuousOn hf.continuousOn
  have hc : IsClosed {x | f (T x) = f x} := isClosed_eq (hf.comp hT) hf
  exact closure_minimal he hc

end OQ14.Packet05PhaseSymmetry
#print axioms OQ14.Packet05PhaseSymmetry.continuous_phase_symmetry

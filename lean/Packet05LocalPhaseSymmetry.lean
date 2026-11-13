import Packet05PhaseGluing

/-! Local a.e. phase symmetry extends to the one-sided continuous trace.
The neighborhood is open so artificial observation boundaries cause no gap. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05LocalPhaseSymmetry
open MeasureTheory Set Maxwell

theorem local_phase_symmetry (U V : Set Space) (hU : IsOpen U) (hV : IsOpen V)
    (f : Space → ℝ) (hf : ContinuousOn f (closure U ∩ V))
    (T : Space → Space) (hT : Continuous T)
    (hmap : MapsTo T (closure U ∩ V) (closure U ∩ V))
    (hae : (f ∘ T) =ᵐ[volume.restrict (U ∩ V)] f) :
    EqOn (f ∘ T) f (closure U ∩ V) := by
  have hsub : U ∩ V ⊆ closure U ∩ V := fun _ hx => ⟨subset_closure hx.1,hx.2⟩
  have hfc : ContinuousOn (f ∘ T) (closure U ∩ V) := hf.comp hT.continuousOn hmap
  have he : EqOn (f ∘ T) f (U ∩ V) :=
    Measure.eqOn_open_of_ae_eq hae (hU.inter hV) (hfc.mono hsub) (hf.mono hsub)
  exact he.of_subset_closure hfc hf hsub (Packet05PhaseGluing.closure_inter_open hV)

end OQ14.Packet05LocalPhaseSymmetry
#print axioms OQ14.Packet05LocalPhaseSymmetry.local_phase_symmetry

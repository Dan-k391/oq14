import Packet05PhaseGluing

/-! A uniform a.e. physical bound on an open collar also controls continuous
one-sided phase traces there, even when they are only locally continuous. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhaseAEBound
open MeasureTheory Set Maxwell

theorem phase_ae_bound (U V : Set Space) (hU : IsOpen U) (hV : IsOpen V)
    (f a : Space → ℝ) (hf : ContinuousOn f (closure U ∩ V)) (B : ℝ)
    (hfa : f =ᵐ[volume.restrict (U ∩ V)] a)
    (ha : ∀ᵐ x ∂volume.restrict V, a x ≤ B) :
    ∀ x ∈ closure U ∩ V, f x ≤ B := by
  have hsub : U ∩ V ⊆ closure U ∩ V := fun x hx => ⟨subset_closure hx.1,hx.2⟩
  have hbound : ∀ᵐ x ∂volume.restrict (U ∩ V), a x ≤ B :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right ha
  have he : (fun x => min (f x) B) =ᵐ[volume.restrict (U ∩ V)] f := by
    filter_upwards [hfa,hbound] with x hx hb
    exact min_eq_left (hx.trans_le hb)
  have hc : ContinuousOn (fun x => min (f x) B) (closure U ∩ V) := hf.inf continuousOn_const
  have hEq := Measure.eqOn_open_of_ae_eq he (hU.inter hV) (hc.mono hsub) (hf.mono hsub)
  have hEq' := hEq.of_subset_closure hc hf hsub (Packet05PhaseGluing.closure_inter_open hV)
  intro x hx
  rw [←hEq' hx]
  exact min_le_right _ _

end OQ14.Packet05PhaseAEBound
#print axioms OQ14.Packet05PhaseAEBound.phase_ae_bound

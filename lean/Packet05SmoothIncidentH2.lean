import Packet05ActualHostModeGraph

/-! Every smooth compactly supported incident-field component has an actual
H² L² representative, ready to add to the Green correction. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05SmoothIncidentH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05GraphPiolaH2

theorem compact_smooth_h2 (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ U : L2Scalar, HasH2 U ∧ (U : Space → ℂ) =ᵐ[volume] f := by
  let s := FourierL2.compactSmoothSchwartz f hf hc
  refine ⟨FourierL2.embed s, ?_, ?_⟩
  · refine ⟨fun i => FourierL2.embed (GradientProjection.pderivative i s),
      fun i j => FourierL2.embed (GradientProjection.pderivative j (GradientProjection.pderivative i s)), ?_, ?_⟩
    · intro i
      exact schwartz_hasWeakPartial s i
    · intro i j
      exact schwartz_hasWeakPartial (GradientProjection.pderivative i s) j
  · exact FourierL2.embed_ae s

end OQ14.Packet05SmoothIncidentH2
#print axioms OQ14.Packet05SmoothIncidentH2.compact_smooth_h2

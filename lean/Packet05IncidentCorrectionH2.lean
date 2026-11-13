import Packet05SmoothIncidentH2

/-! Smooth incident fields can be added to the H² Green correction without
changing the transmission forcing regularity. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05IncidentCorrectionH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05GraphPiolaH2 OQ14.Packet05LocalizedAnisotropic OQ14.Packet05SmoothIncidentH2

theorem h2_add (u v : L2Scalar) (hu : HasH2 u) (hv : HasH2 v) : HasH2 (u+v) := by
  obtain ⟨G,H,hG,hH⟩ := hu
  obtain ⟨G',H',hG',hH'⟩ := hv
  exact ⟨fun i => G i+G' i, fun i j => H i j+H' i j,
    fun i => weak_partial_add _ _ _ _ i (hG i) (hG' i),
    fun i j => weak_partial_add _ _ _ _ j (hH i j) (hH' i j)⟩

theorem incident_plus_correction_h2 (u : L2Scalar) (hu : HasH2 u)
    (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ U : L2Scalar, HasH2 U ∧ (U : Space → ℂ) =ᵐ[volume] fun x => u x + f x := by
  obtain ⟨v,hv,hv'⟩ := compact_smooth_h2 f hf hc
  refine ⟨u+v,h2_add u v hu hv,?_⟩
  filter_upwards [Lp.coeFn_add u v,hv'] with x ha hb
  rw [ha]
  simp only [Pi.add_apply,hb]

end OQ14.Packet05IncidentCorrectionH2
#print axioms OQ14.Packet05IncidentCorrectionH2.h2_add
#print axioms OQ14.Packet05IncidentCorrectionH2.incident_plus_correction_h2

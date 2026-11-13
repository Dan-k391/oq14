import Packet07DrivenPlacedRegionalHCurl

/-! Direct H(curl) upgrade of the actual Maxwell identity exported by PlaneFinal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenExportedHCurl
open MeasureTheory Set Metric Maxwell Packet07DrivenPlacedHCurl Packet07DrivenPlacedRegionalHCurl
  Packet07DrivenRigidHotspot
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem placed_regional_hcurl_of_maxwell {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k s target : ℝ) (hs : 0 < s) (input : Input)
    (j : ℕ) (θ φ : ℝ) (a b : Space) (Ω : Set Space) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hMax : Packet06ComplexAffine.TestMaxwellC (target : ℂ) (dielectric s a b θ φ (g.rounded j))
      (field θ φ a (Packet07AffineMaxwell.affineField s b (g.electric k j input)))
      (field θ φ a (Packet07AffineMaxwell.affineField s b (g.magnetic k j input)))) :
    ∃ e h : DomainCurl.HCurl Ω,
      (∀ i, (e.val.1 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => field θ φ a (Packet07AffineMaxwell.affineField s b (g.electric k j input)) x i) ∧
      (∀ i, (h.val.1 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => field θ φ a (Packet07AffineMaxwell.affineField s b (g.magnetic k j input)) x i) ∧
      WeakConservation.WeakMaxwell target (fun _ => 1) (dielectric s a b θ φ (g.rounded j)) e h := by
  obtain ⟨hE,hH⟩ := placed_fields g k s hs input j θ φ a b
  have hD := dielectric_electric g k s hs input j θ φ a b
  exact MaterialHCurl.exists_regional_fields hΩ target _ _ _
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hE i) Ω hbounded)
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hH i) Ω hbounded)
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hD i) Ω hbounded) hMax
end OQ14.Packet07DrivenExportedHCurl
#print axioms OQ14.Packet07DrivenExportedHCurl.placed_regional_hcurl_of_maxwell

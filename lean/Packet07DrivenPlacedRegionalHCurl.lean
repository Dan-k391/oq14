import Packet07DrivenPlacedHCurl
import Packet07DrivenActualGood
import Packet07DrivenAffineGood

/-! Literal placed E, H and εE have regional L² and genuine H(curl) graphs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet07DrivenPlacedRegionalHCurl
open MeasureTheory Set Metric Maxwell Packet07DrivenPlacedHCurl Packet07DrivenFrameMaxwell
  Packet07DrivenRigidHotspot Packet07DrivenLocalL2Transport
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

def dielectric (s : ℝ) (a b : Space) (θ φ : ℝ) (c : StaticCoefficient.Coefficient) : Space → ℝ :=
  fun x => MaterialMaxwell.dielectric c (Packet07AffineGeometry.map s b ((Packet07PlaneFrame.normalRotation θ φ).symm (x-a)))

theorem dielectric_electric {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k s : ℝ) (hs : 0 < s) (input : Input)
    (j : ℕ) (θ φ : ℝ) (a b : Space) :
    ∀ i, LocalL2 (fun x => (dielectric s a b θ φ (g.rounded j) x : ℂ) *
      field θ φ a (Packet07AffineMaxwell.affineField s b (g.electric k j input)) x i) := by
  have hE := (placed_fields g k s hs input j θ φ a b).1
  have hmeas : Measurable (dielectric s a b θ φ (g.rounded j)) := by
    unfold dielectric Packet07AffineGeometry.map
    exact (MaterialHCurl.dielectric_measurable _).comp
      ((measurable_const_smul s).comp (((Packet07PlaneFrame.normalRotation θ φ).symm.continuous.measurable.comp (measurable_id.sub measurable_const)).sub measurable_const))
  have hb : ∀ x, ‖dielectric s a b θ φ (g.rounded j) x‖ ≤ 1+(g.rounded j).bound := by
    intro x
    exact MaterialHCurl.dielectric_norm_bound _ _
  intro i T
  exact MaterialHCurl.coefficient_mul_memLp (closedBall 0 T) _ hmeas _ hb _ (hE i T)

theorem placed_regional_hcurl {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k s : ℝ) (hs : 0 < s) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) (j : ℕ)
    (θ φ : ℝ) (a b : Space) (Ω : Set Space) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ e h : DomainCurl.HCurl Ω,
      (∀ i, (e.val.1 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => field θ φ a (Packet07AffineMaxwell.affineField s b (g.electric k j input)) x i) ∧
      (∀ i, (h.val.1 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => field θ φ a (Packet07AffineMaxwell.affineField s b (g.magnetic k j input)) x i) ∧
      WeakConservation.WeakMaxwell (s*k) (fun _ => 1) (dielectric s a b θ φ (g.rounded j)) e h := by
  obtain ⟨hE,hH⟩ := placed_fields g k s hs input j θ φ a b
  have hD := dielectric_electric g k s hs input j θ φ a b
  have hgood := Packet07DrivenActualGood.actual_good g k input hk j
  have hgood' := Packet07DrivenAffineGood.affine_good s hs b k _ _ _ hgood
  have hM := Packet07DrivenRigidFields.rigid_maxwell θ φ (s*k) a _ _ _ hgood'
  apply MaterialHCurl.exists_regional_fields hΩ (s*k) _ _ _
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hE i) Ω hbounded)
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hH i) Ω hbounded)
    (fun i => MaterialHCurl.memLp_bounded_of_balls _ (hD i) Ω hbounded)
  exact hM
end OQ14.Packet07DrivenPlacedRegionalHCurl
#print axioms OQ14.Packet07DrivenPlacedRegionalHCurl.dielectric_electric
#print axioms OQ14.Packet07DrivenPlacedRegionalHCurl.placed_regional_hcurl

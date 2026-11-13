import Packet07DrivenUniformAllHotspots
import Packet07DrivenUniformComponentPeak
import Packet07PlanarSetup

/-! One actual normalized illumination produces all driven hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet07DrivenUniformSelectedHotspots
open Filter MeasureTheory Set Metric Packet07PlanarSetup Packet07DrivenUniformHotspot Packet05ActualMaximum
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem one_input_all_hotspots (N : ℕ) (hN : 0 < N)
    (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ g : Setup N P d t, ∃ δ : ℝ, 0 < δ ∧ ∀ freq : ℝ, 0 < freq → freq < δ →
      ∃ input : Input, input ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK freq input) atTop (𝓝 1) ∧
        ∃ B : Fin N → ℝ, (∀ i, 0 ≤ B i) ∧ ∀ M : Fin N → ℝ,
          ∀ᶠ j : ℕ in atTop, ∀ i,
            HotspotAbove (g.electric freq j input) (CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
              (g.centers i) (g.radius/2) (M i) (B i) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨g⟩ := Packet07PlanarSetup.exists_setup N P hP hne d t hd ht ht1
  have hb0 : ∀ i : Fin N, 0 < g.radius/2 := fun _ => half_pos g.radius_pos
  have hb : ∀ i : Fin N, g.radius/2 < g.radii i := fun _ => by dsimp [Setup.radii]; linarith [g.radius_pos]
  have hν : ∀ i : Fin N, (g.dataFamily i).exponent < 1 := fun _ => g.exponent_lt_one
  have hra : ∀ i : Fin N, 0 ≤ g.radii i := fun _ => g.radius_pos.le
  have hgeom : ∀ i j : Fin N, i ≠ j → g.radii i + g.radii j < dist (g.centers i) (g.centers j) := g.separation
  have hR : ∀ i : Fin N, ConicalCommonMaterial.outer g.dataFamily g.centers i ⊆ closedBall (0 : Space) g.enclosing := g.outer_enclosed
  have hai : ∀ i : Fin N, g.radii i < (g.dataFamily i).cutoff.rIn := fun _ => g.radius_in
  obtain ⟨δ,hδ,hex⟩ := ConicalCommonBinaryPeaks.one_input_rounded_superlevels g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.enclosing
    (fun _ => g.radius/2) g.enclosing_nonnegative le_rfl hb0 hb hν hra hgeom g.balls_enclosed hR hai
  have hrad : 0 < MaterialVolumeLimit.commonRadius d g.enclosing :=
    MaterialVolumeLimit.commonRadius_positive d g.enclosing hd.le
  refine ⟨g,min δ (MaterialVolumeLimit.commonRadius d g.enclosing),lt_min hδ hrad,?_⟩
  intro freq hfreq hsmall
  obtain ⟨_,input,hin,hpower,_,_,hpeaks⟩ := hex freq hfreq (hsmall.trans_le (min_le_left _ _))
  have hcommon : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing := by
    rw [abs_of_pos hfreq]
    exact (hsmall.trans_le (min_le_right _ _)).le
  refine ⟨input,hin,hpower,?_⟩
  apply Packet07DrivenUniformAllHotspots.eventually_all_hotspots g freq hfreq.ne' input hcommon
    (fun _ => g.radius/2) hb0 (fun _ => by linarith [g.radius_pos])
  intro i M
  obtain ⟨l,hl⟩ := hpeaks i (g.radius/2) (hb0 i) le_rfl
  filter_upwards [hl M] with j hj
  have hh := Packet07DrivenUniformComponentPeak.positive_component_peak (g.electric freq j input)
    (ball (g.centers i) (g.radius/2)) l M hj
  exact lt_of_lt_of_le hh (Measure.restrict_mono_set volume
    (ball_subset_closedBall : ball (g.centers i) (g.radius/2) ⊆ closedBall (g.centers i) (g.radius/2)) _)
end OQ14.Packet07DrivenUniformSelectedHotspots
#print axioms OQ14.Packet07DrivenUniformSelectedHotspots.one_input_all_hotspots

import Packet07DrivenUniformHotspot

/-! The same late driven device realizes all finitely many isolated hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformAllHotspots
open MeasureTheory Set Filter Metric Maxwell Packet05ActualMaximum Packet07DrivenUniformHotspot
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem eventually_all_hotspots {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0) (input : Input)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < g.radius)
    (hpeak : ∀ i M, ∀ᶠ j : ℕ in atTop,
      0 < (volume.restrict (closedBall (g.centers i) (r i)))
        {y | M < physicalAmplitude (fun k x => g.electric freq j input x k) y}) :
    ∃ B : Fin N → ℝ, (∀ i, 0 ≤ B i) ∧ ∀ M : Fin N → ℝ,
      ∀ᶠ j : ℕ in atTop, ∀ i,
        HotspotAbove (g.electric freq j input) (CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
          (g.centers i) (r i) (M i) (B i) := by
  classical
  have hex i := eventually_actual_hotspot g freq hfreq0 input hfreq i (r i) (hr i) (hrR i)
  choose B hB hevent using hex
  refine ⟨B,hB,?_⟩
  intro M
  have hp : ∀ᶠ j : ℕ in atTop, ∀ i,
      0 < (volume.restrict (closedBall (g.centers i) (r i)))
        {y | max (M i) (2*B i) < physicalAmplitude (fun k x => g.electric freq j input x k) y} :=
    Filter.eventually_all.mpr (fun i => hpeak i (max (M i) (2*B i)))
  filter_upwards [Filter.eventually_all.mpr hevent,hp] with j hj hp i
  exact hj i (M i) (hp i)
end OQ14.Packet07DrivenUniformAllHotspots
#print axioms OQ14.Packet07DrivenUniformAllHotspots.eventually_all_hotspots

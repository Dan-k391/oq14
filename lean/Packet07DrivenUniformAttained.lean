import Packet07DrivenUniformCompactActual
import Packet05BinaryPhaseMaximum
import Packet07BoundaryNull

/-! Positive-volume driven peaks force literal material-side attained maxima. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenUniformAttained
open MeasureTheory Set Filter Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem eventually_attained_above_peak {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (k : ℝ) (hk0 : k ≠ 0) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) :
    ∀ᶠ j : ℕ in atTop, ∀ (K : Set Space), IsCompact K → K.Nonempty → ∀ M : ℝ,
      0 < (volume.restrict K) {y | M < physicalAmplitude (fun i x => g.electric k j input x i) y} →
      let body := CommonBinaryInterface.body g.dataFamily g.radii g.centers j
      ∃ (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space),
        (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
        (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
        (∀ i, (fun y => g.electric k j input y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
        (∀ i, (fun y => g.electric k j input y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) ∧
        x ∈ K ∩ phaseDomain body b ∧ M < physicalAmplitude (phaseField inside outside b) x ∧
        ∀ b' y, y ∈ K ∩ phaseDomain body b' →
          physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x := by
  filter_upwards [Packet07DrivenUniformCompactActual.eventually_compact_branches g k hk0 input hk,
    CommonBinaryInterface.eventually_body_smooth g.dataFamily g.radii g.centers g.radii_pos g.radii_outer g.outer_sep]
    with j hbranches hcert K hK hne M hpeak
  dsimp only
  let body := CommonBinaryInterface.body g.dataFamily g.radii g.centers j
  obtain ⟨inside,outside,hi,ho,he,he'⟩ := hbranches K hK
  have hb : IsOpen body := CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j
  have hn : volume (frontier body)=0 := Packet07BoundaryNull.bounded_regular_body_boundary_null body 0 g.enclosing
    (CommonBinaryInterface.body_support g.dataFamily g.radii g.centers g.radii_pos g.radii_outer g.enclosing g.outer_enclosed j) hcert
  obtain ⟨b,x,hx,hh,hm⟩ := attained_above_peak body K hb hK hne hn (g.electric k j input) inside outside hi ho he he' M hpeak
  exact ⟨inside,outside,b,x,hi,ho,he,he',hx,hh,hm⟩
end OQ14.Packet07DrivenUniformAttained
#print axioms OQ14.Packet07DrivenUniformAttained.eventually_attained_above_peak

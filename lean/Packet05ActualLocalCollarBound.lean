import Packet05TwoPhaseAEFieldBound

/-! Every actual fixed rounded-family material chart has one eventual
componentwise physical-field bound near each physical chart point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05ActualLocalCollarBound
open MeasureTheory Set Filter Maxwell Packet05PhysicalChartBranches Packet05FiniteFixedAtlas Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_local_chart_bound {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (x : Space) (hx : x ∈ physical chart)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0) :
    ∃ (O : Set Space) (B : ℝ), IsOpen O ∧ x ∈ O ∧ O ⊆ physical chart ∧ 0 ≤ B ∧
      ∀ᶠ j in atTop, ∀ k, ∀ᵐ y ∂volume, y ∈ O →
        ‖Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k‖ ≤ B := by
  obtain ⟨T,B,hT,hp,hTsub,hB,hfamily⟩ := Packet05FixedChartUniformField.fixed_chart_uniform_field
    n hn g η hη chart (physicalFlatMap chart.up chart.axis chart.graph x) hx z v z0 v0 hzlim hvlim hz hmode
  let O : Set Space := physicalFlatMap chart.up chart.axis chart.graph ⁻¹' T
  have hO : IsOpen O := hT.preimage (physicalFlat_continuous chart.up chart.axis chart.graph (chart.regular.of_le (by decide)))
  refine ⟨O,B,hO,hp,preimage_mono hTsub,hB,?_⟩
  filter_upwards [hfamily] with j hj
  obtain ⟨lower,upper,hl,hu,hle,hue,hlb,hub⟩ := hj
  exact Packet05TwoPhaseAEFieldBound.two_phase_ae_bound chart.up chart.axis chart.graph
    (chart.regular.of_le (by decide)) T hT _ lower upper B hle hue hlb hub

end OQ14.Packet05ActualLocalCollarBound
#print axioms OQ14.Packet05ActualLocalCollarBound.actual_local_chart_bound

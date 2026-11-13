import Packet05GraphBoundaryNull
import Packet05HighMaximum

/-! The two actual sides of any continuous graph cover almost every point;
this feeds the positive-volume-to-attained-maximum argument. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphPhaseCover
open MeasureTheory Set OQ14.ConicalJunctionPhysical
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphBoundaryNull

theorem continuous_graph_phase_cover_ae (g : Plane → ℝ) (hg : Continuous g)
    (K Vminus Vplus : Set Space) (hK : MeasurableSet K)
    (hcover : ∀ x ∈ K, x 2 ≠ g (horizontal x) → x ∈ Vminus ∨ x ∈ Vplus) :
    ∀ᵐ x ∂volume.restrict K, x ∈ Vminus ∨ x ∈ Vplus := by
  have hgraph : ∀ᵐ x : Space ∂volume, x 2 ≠ g (horizontal x) := by
    rw [ae_iff]
    simpa using continuous_graph_volume_zero g hg
  filter_upwards [ae_restrict_of_ae hgraph, ae_restrict_mem hK] with x hx hxK
  exact hcover x hxK hx

end OQ14.Packet05GraphPhaseCover
#print axioms OQ14.Packet05GraphPhaseCover.continuous_graph_phase_cover_ae

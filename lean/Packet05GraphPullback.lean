import Packet05GraphVolume

/-! Actual L² pullback and change of variables through the graph chart. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphPullback
open MeasureTheory OQ14.ConicalJunctionPhysical
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05GraphVolume

def pullback (g : Plane → ℝ) (hg : Continuous g) (u : WeakCurl.L2Scalar) : WeakCurl.L2Scalar :=
  Lp.compMeasurePreserving (graphMap (liftedHeight g)) (graph_map_volume_preserving g hg) u

theorem pullback_ae (g : Plane → ℝ) (hg : Continuous g) (u : WeakCurl.L2Scalar) :
    (fun x => pullback g hg u x) =ᵐ[volume] fun x => u (graphMap (liftedHeight g) x) :=
  Lp.coeFn_compMeasurePreserving u (graph_map_volume_preserving g hg)

theorem pullback_norm (g : Plane → ℝ) (hg : Continuous g) (u : WeakCurl.L2Scalar) :
    ‖pullback g hg u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (graph_map_volume_preserving g hg)

theorem graph_change_of_variables (g : Plane → ℝ) (hg : Continuous g) (f : Space → ℂ) :
    (∫ x, f (graphMap (liftedHeight g) x)) = ∫ x, f x := by
  apply (graph_map_volume_preserving g hg).integral_comp _ f
  exact (physicalGraphHomeomorph g hg).measurableEmbedding

end OQ14.Packet05GraphPullback
#print axioms OQ14.Packet05GraphPullback.pullback_ae
#print axioms OQ14.Packet05GraphPullback.pullback_norm
#print axioms OQ14.Packet05GraphPullback.graph_change_of_variables

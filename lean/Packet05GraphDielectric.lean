import Packet05GraphConstitutive
import FlatDifferenceCoercivity
import Packet05GraphChartHomeomorph

/-! A binary graph-interface coefficient becomes the actual flat binary
coefficient under the physical graph chart. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphDielectric
open OQ14.ConicalJunctionPhysical OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphChartHomeomorph
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def graphDielectric (g : Plane → ℝ) (d : ℝ) (x : Space) : ℝ :=
  if x 2 < g (horizontal x) then 1 else 1+d

theorem graph_dielectric_pullback (g : Plane → ℝ) (d : ℝ) (x : Space) :
    graphDielectric g d (graphMap (liftedHeight g) x) = FlatDifferenceCoercivity.dielectric d x := by
  unfold graphDielectric FlatDifferenceCoercivity.dielectric
  have hh := graph_map_height (liftedHeight g) (liftedHeight_normal_invariant g) x
  change graphMap (liftedHeight g) x 2 - g (horizontal (graphMap (liftedHeight g) x)) = x 2 at hh
  split_ifs <;> linarith

end OQ14.Packet05GraphDielectric
#print axioms OQ14.Packet05GraphDielectric.graph_dielectric_pullback

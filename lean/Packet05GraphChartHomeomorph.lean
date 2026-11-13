import Packet05GraphChartMap

/-! The graph map is a homeomorphism and sends the two actual sides of a
graph interface to the corresponding open half-spaces. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphChartHomeomorph
open OQ14.Maxwell OQ14.Packet05GraphChartMap

def graphHomeomorph (γ : Space → ℝ) (hc : Continuous γ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) : Space ≃ₜ Space where
  toFun := graphMap γ
  invFun := inverseGraphMap γ
  left_inv := graph_map_left_inverse γ hγ
  right_inv := graph_map_right_inverse γ hγ
  continuous_toFun := continuous_id.add (hc.smul continuous_const)
  continuous_invFun := continuous_id.sub (hc.smul continuous_const)

theorem graph_map_height (γ : Space → ℝ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) (x : Space) :
    graphMap γ x 2 - γ (graphMap γ x) = x 2 := by
  change (x + γ x • basis 2) 2 - γ (x + γ x • basis 2) = x 2
  rw [hγ]
  simp [basis, EuclideanSpace.single_apply, PiLp.add_apply, PiLp.smul_apply]

theorem graph_map_positive_side (γ : Space → ℝ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) (x : Space) :
    0 < graphMap γ x 2 - γ (graphMap γ x) ↔ 0 < x 2 := by
  rw [graph_map_height γ hγ x]

theorem graph_map_negative_side (γ : Space → ℝ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) (x : Space) :
    graphMap γ x 2 - γ (graphMap γ x) < 0 ↔ x 2 < 0 := by
  rw [graph_map_height γ hγ x]

end OQ14.Packet05GraphChartHomeomorph
#print axioms OQ14.Packet05GraphChartHomeomorph.graph_map_height
#print axioms OQ14.Packet05GraphChartHomeomorph.graph_map_positive_side
#print axioms OQ14.Packet05GraphChartHomeomorph.graph_map_negative_side

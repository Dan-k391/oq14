import Packet05GraphChartMatrix
import Maxwell

/-! The graph-flattening map, its inverse and its actual Fréchet derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphChartMap
open OQ14.Maxwell OQ14.Packet05GraphChartMatrix

def graphMap (γ : Space → ℝ) (x : Space) : Space := x + γ x • basis 2

def inverseGraphMap (γ : Space → ℝ) (x : Space) : Space := x - γ x • basis 2

theorem graph_map_left_inverse (γ : Space → ℝ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) (x : Space) :
    inverseGraphMap γ (graphMap γ x) = x := by
  simp only [inverseGraphMap, graphMap, hγ]
  abel

theorem graph_map_right_inverse (γ : Space → ℝ)
    (hγ : ∀ (x : Space) (t : ℝ), γ (x + t • basis 2) = γ x) (x : Space) :
    graphMap γ (inverseGraphMap γ x) = x := by
  have hg : γ (x - γ x • basis 2) = γ x := by
    simpa only [neg_smul, sub_eq_add_neg] using hγ x (-γ x)
  simp only [graphMap, inverseGraphMap, hg]
  abel

theorem graph_map_has_fderiv (γ : Space → ℝ) (x : Space) (D : Space →L[ℝ] ℝ)
    (hγ : HasFDerivAt γ D x) :
    HasFDerivAt (graphMap γ) (ContinuousLinearMap.id ℝ Space + D.smulRight (basis 2)) x := by
  simpa only [graphMap] using (hasFDerivAt_id x).add (hγ.smul_const (basis 2))

theorem graph_derivative_coordinate (D : Space →L[ℝ] ℝ) (i j : Fin 3)
    (hn : D (basis 2) = 0) :
    (ContinuousLinearMap.id ℝ Space + D.smulRight (basis 2)) (basis j) i =
      jacobian (D (basis 0)) (D (basis 1)) i j := by
  simp only [basis] at hn
  fin_cases i <;> fin_cases j <;>
    simp [jacobian, basis, EuclideanSpace.single_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, hn]

end OQ14.Packet05GraphChartMap
#print axioms OQ14.Packet05GraphChartMap.graph_map_left_inverse
#print axioms OQ14.Packet05GraphChartMap.graph_map_right_inverse
#print axioms OQ14.Packet05GraphChartMap.graph_map_has_fderiv
#print axioms OQ14.Packet05GraphChartMap.graph_derivative_coordinate

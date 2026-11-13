import Packet07BoundaryGraph

/-! Cartesian coordinate swaps and split coordinates for local boundary charts. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryCoordinates
open Packet07PhysicalLobes
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothCapGraph.Plane
abbrev Point := Plane × ℝ

def swap (i : Fin 3) (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun j => x (Equiv.swap i 2 j))

def swapLinear (i : Fin 3) : Space →ₗ[ℝ] Space where
  toFun := swap i
  map_add' x y := by ext j; simp [swap, PiLp.add_apply]
  map_smul' c x := by ext j; simp [swap, PiLp.smul_apply]

def swapCLM (i : Fin 3) : Space →L[ℝ] Space := (swapLinear i).toContinuousLinearMap

theorem swap_involution (i : Fin 3) (x : Space) : swap i (swap i x) = x := by
  ext j
  change x ((Equiv.swap i 2) ((Equiv.swap i 2) j)) = x j
  rw [Equiv.swap_apply_self]

theorem swap_axis (i : Fin 3) : swap i (EuclideanSpace.single 2 1) = EuclideanSpace.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [swap, Equiv.swap_apply_def, EuclideanSpace.single_apply]

def chart (i : Fin 3) (x : Space) : Point := ConicalJunctionPhysical.split (swap i x)
def unchart (i : Fin 3) (q : Point) : Space := swap i (unsplit q)
def unchartCLM (i : Fin 3) : Point →L[ℝ] Space := (swapCLM i).comp unsplitLinear.toContinuousLinearMap

theorem unchart_chart (i : Fin 3) (x : Space) : unchart i (chart i x) = x := by
  simp [chart, unchart, unsplit_split, swap_involution]

theorem chart_unchart (i : Fin 3) (q : Point) : chart i (unchart i q) = q := by
  simp [chart, unchart, swap_involution, split_unsplit]

theorem unchart_vertical (i : Fin 3) : unchart i (0,1) = EuclideanSpace.single i 1 := by
  have hu : unsplit (0,1) = EuclideanSpace.single 2 1 := by
    ext j
    fin_cases j <;> simp [unsplit, EuclideanSpace.single_apply]
  simp [unchart, hu, swap_axis]

end OQ14.Packet07BoundaryCoordinates
#print axioms OQ14.Packet07BoundaryCoordinates.swap_involution
#print axioms OQ14.Packet07BoundaryCoordinates.swap_axis
#print axioms OQ14.Packet07BoundaryCoordinates.unchart_chart
#print axioms OQ14.Packet07BoundaryCoordinates.chart_unchart
#print axioms OQ14.Packet07BoundaryCoordinates.unchart_vertical

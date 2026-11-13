import Packet05GraphChartHomeomorph
import ConicalJunctionPhysical

/-! Instantiate the graph chart with a two-dimensional height function in the
same physical coordinates used by the rounded conical construction. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhysicalGraphChart
open OQ14.ConicalJunctionPhysical OQ14.Packet05GraphChartHomeomorph
abbrev Plane := OQ14.ConicalSmoothJunction.Plane
open OQ14.Maxwell (basis)

def liftedHeight (g : Plane → ℝ) (x : Space) : ℝ := g (horizontal x)

theorem horizontal_normal_invariant (x : Space) (t : ℝ) :
    horizontal (x + t • basis 2) = horizontal x := by
  ext i
  fin_cases i <;> simp [horizontal, basis, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply]

theorem liftedHeight_normal_invariant (g : Plane → ℝ) (x : Space) (t : ℝ) :
    liftedHeight g (x + t • basis 2) = liftedHeight g x := by
  simp [liftedHeight, horizontal_normal_invariant]

theorem liftedHeight_continuous (g : Plane → ℝ) (hg : Continuous g) :
    Continuous (liftedHeight g) :=
  hg.comp horizontalLinear.continuous_of_finiteDimensional

def physicalGraphHomeomorph (g : Plane → ℝ) (hg : Continuous g) : Space ≃ₜ Space :=
  graphHomeomorph (liftedHeight g) (liftedHeight_continuous g hg) (liftedHeight_normal_invariant g)

end OQ14.Packet05PhysicalGraphChart
#print axioms OQ14.Packet05PhysicalGraphChart.horizontal_normal_invariant
#print axioms OQ14.Packet05PhysicalGraphChart.liftedHeight_normal_invariant
#print axioms OQ14.Packet05PhysicalGraphChart.liftedHeight_continuous

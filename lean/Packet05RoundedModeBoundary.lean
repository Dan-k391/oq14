import Packet05BoundaryMaterialMode
import Packet05RoundedModeMaterial

/-! Actual rounded modal cone interfaces have continuous physical phase fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RoundedModeBoundary
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05RoundedModeMaterial
open Packet05BoundaryMaterialMode
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_rounded_cone_phase_representatives {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ j : ℕ in atTop, ∀ (z : ℂ), z ≠ 0 → ∀ (mode : VectorFourier.VectorL2),
      (∀ x : Space, x ∉ closedBall 0 1 →
        (rounded n hn g η hη j).value (VectorFourier.coordinateMap x)=0) →
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 mode=0 →
      ∀ x ∈ frontier (body g j), HasPhaseRepresentatives
        (Packet06ComplexElectric.electric z
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) mode)
          (DynamicVolume.source (rounded n hn g η hη j) mode)) (body g j) x := by
  filter_upwards [eventually_boundary_certificate g] with j hcert z hz mode hc hmode x hx
  have hhost : (n^2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sq_pos_of_pos (by linarith : 0 < n)))
  exact boundary_material_mode (rounded n hn g η hη j) z hz 1 mode hc hmode (body g j) x hx
    (hcert x hx) (n^2 : ℂ) hhost η hη
    (local_cone_material n hn g η hη j x (boundary_inside_sphere g j x hx))

end OQ14.Packet05RoundedModeBoundary
#print axioms OQ14.Packet05RoundedModeBoundary.eventually_rounded_cone_phase_representatives

import Packet05RoundedModeSupport

/-! Literal rounded modes have phase representatives at their actual cone
interfaces, with no material, geometric, or support premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RoundedModeActualPhases
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05BoundaryMaterialMode
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_actual_cone_phase_representatives {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ j : ℕ in atTop, ∀ (z : ℂ), z ≠ 0 → ∀ (mode : VectorFourier.VectorL2),
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 mode=0 →
      ∀ x ∈ frontier (body g j), HasPhaseRepresentatives
        (Packet06ComplexElectric.electric z
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) mode)
          (DynamicVolume.source (rounded n hn g η hη j) mode)) (body g j) x := by
  filter_upwards [Packet05RoundedModeBoundary.eventually_rounded_cone_phase_representatives n hn g η hη] with j hj z hz mode hmode x hx
  exact hj z hz mode (Packet05RoundedModeSupport.rounded_support n hn g η hη j) hmode x hx

end OQ14.Packet05RoundedModeActualPhases
#print axioms OQ14.Packet05RoundedModeActualPhases.eventually_actual_cone_phase_representatives

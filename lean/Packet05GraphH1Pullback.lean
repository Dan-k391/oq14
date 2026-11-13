import Packet05GraphTangentialWeakDerivative

/-! The graph pullback of an actual H¹ scalar has all three actual weak
partials, assembled into a single gradient field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphH1Pullback
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphTangentialWeakDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def pulledGradient (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (U : L2Vector)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) : L2Vector := fun i =>
  pullback g hg.continuous (U i) + slopeMul g hg i (B i) (hB i) (pullback g hg.continuous (U 2))

theorem graph_pullback_h1 (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (u : L2Scalar)
    (U : L2Vector) (hU : ∀ i, HasWeakPartial u (U i) i)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    ∀ i, HasWeakPartial (pullback g hg.continuous u) (pulledGradient g hg U B hB i) i := by
  intro i
  exact pullback_tangential_weak_partial g hg u (U i) (U 2) i (hU i) (hU 2) (B i) (hB i)

end OQ14.Packet05GraphH1Pullback
#print axioms OQ14.Packet05GraphH1Pullback.graph_pullback_h1

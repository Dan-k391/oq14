import Packet05BoundedWeakMultiplier
import Packet05LocalizedAnisotropic

/-! H² of an actual scalar survives a smooth graph pullback; the derivative
of the graph slope is included in the explicit second weak derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphH2Pullback
open MeasureTheory OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurlCompact
  OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05BoundedWeakMultiplier OQ14.Packet05LocalizedAnisotropic
open OQ14.Maxwell (dcoord)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_pullback_h2 (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (u : L2Scalar)
    (G : L2Vector) (H : Fin 3 → L2Vector)
    (hG : ∀ i, HasWeakPartial u (G i) i)
    (hH : ∀ i j, HasWeakPartial (G i) (H i j) j)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (hdi : ∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume) :
    ∃ K : Fin 3 → Fin 3 → L2Scalar,
      (∀ i, HasWeakPartial (pullback g hg.continuous u) (pulledGradient g hg G B hB i) i) ∧
      (∀ i j, HasWeakPartial (pulledGradient g hg G B hB i) (K i j) j) := by
  have hfirst := graph_pullback_h1 g hg u G hG B hB
  have hp (i j : Fin 3) := graph_pullback_h1 g hg (G i) (H i) (hH i) B hB j
  have hs (i j : Fin 3) : HasWeakPartial
      (slopeMul g hg i (B i) (hB i) (pullback g hg.continuous (G 2)))
      (boundedMultiply (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i))
        (pulledGradient g hg (H 2) B hB j) +
        boundedMultiply (fun x => dcoord (slopeC g i) x j) (hdi i j)
          (pullback g hg.continuous (G 2))) j := by
    exact bounded_multiplier_weak_partial _ (slopeC_contDiff g hg i) _ j (hdi i j) _ _ (hp 2 j)
  classical
  let K (i j : Fin 3) := pulledGradient g hg (H i) B hB j +
    (boundedMultiply (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i))
        (pulledGradient g hg (H 2) B hB j) +
      boundedMultiply (fun x => dcoord (slopeC g i) x j) (hdi i j)
        (pullback g hg.continuous (G 2)))
  refine ⟨K, hfirst, ?_⟩
  intro i j
  exact weak_partial_add _ _ _ _ j (hp i j) (hs i j)

end OQ14.Packet05GraphH2Pullback
#print axioms OQ14.Packet05GraphH2Pullback.graph_pullback_h2

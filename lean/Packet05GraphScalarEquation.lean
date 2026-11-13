import Packet05GraphPiolaLinear
import Packet05GraphH1Pullback

/-! Transform the actual weak scalar transmission equation with an explicit
L² source; no regularity conclusion is used as a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphScalarEquation
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05GraphL2Constitutive OQ14.Packet05GraphPiolaLinear
  OQ14.Packet05GraphH1Pullback
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_scalar_equation (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (u : L2Scalar) (U P F : L2Vector) (D : L2Scalar) (ε : Space → ℂ)
    (hU : ∀ i, HasWeakPartial u (U i) i)
    (hdiv : HasWeakDivergence P D)
    (hP : ∀ j, (fun y => P j y) =ᵐ[volume] fun y => ε y * U j y + F j y)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    ∃ Q : L2Vector,
      HasWeakDivergence (fun j => Q j + transformedFlux g hg F B hB j) (pullback g hg.continuous D) ∧
      (∀ i, HasWeakPartial (pullback g hg.continuous u) (pulledGradient g hg U B hB i) i) ∧
      ∀ j, (fun x => Q j x) =ᵐ[volume]
        fun x => ε (graphMap (liftedHeight g) x) *
          ∑ i : Fin 3, (Packet05GraphChartMatrix.metric
            (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j i : ℂ) *
              pulledGradient g hg U B hB i x := by
  let R : L2Vector := fun j => P j - F j
  have hR : ∀ j, (fun y => R j y) =ᵐ[volume] fun y => ε y * U j y := by
    intro j
    filter_upwards [hP j, Lp.coeFn_sub (P j) (F j)] with y hp hs
    change (P j - F j : L2Scalar) y = _
    rw [hs]
    simp only [Pi.sub_apply, hp, add_sub_cancel_right]
  let Q : L2Vector := transformedFlux g hg R B hB
  refine ⟨Q, ?_, graph_pullback_h1 g hg u U hU B hB, ?_⟩
  · have he : (fun j => Q j + transformedFlux g hg F B hB j) = transformedFlux g hg P B hB := by
      funext j
      change transformedFlux g hg R B hB j + transformedFlux g hg F B hB j = _
      rw [← transformedFlux_add]
      congr 1
      funext i
      simp [R]
    rw [he]
    exact graph_pullback_weak_divergence g hg P D hdiv B hB
  · intro j
    exact graph_constitutive_l2 g hg U R ε hR B hB j

end OQ14.Packet05GraphScalarEquation
#print axioms OQ14.Packet05GraphScalarEquation.graph_scalar_equation

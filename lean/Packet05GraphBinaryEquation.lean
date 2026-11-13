import Packet05GraphScalarEquation
import Packet05GraphDielectric

/-! Binary graph-interface weak scalar transmission transforms to the flat
binary jump times the graph metric, with its actual source retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphBinaryEquation
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphScalarEquation OQ14.Packet05GraphDielectric
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_binary_scalar_equation (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (d : ℝ)
    (u : L2Scalar) (U P F : L2Vector) (D : L2Scalar)
    (hU : ∀ i, HasWeakPartial u (U i) i) (hdiv : HasWeakDivergence P D)
    (hP : ∀ j, (fun y => P j y) =ᵐ[volume] fun y => (graphDielectric g d y : ℂ) * U j y + F j y)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    ∃ Q : L2Vector,
      HasWeakDivergence (fun j => Q j + transformedFlux g hg F B hB j) (pullback g hg.continuous D) ∧
      (∀ i, HasWeakPartial (pullback g hg.continuous u) (pulledGradient g hg U B hB i) i) ∧
      ∀ j, (fun x => Q j x) =ᵐ[volume]
        fun x => (FlatDifferenceCoercivity.dielectric d x : ℂ) *
          ∑ i : Fin 3, (Packet05GraphChartMatrix.metric
            (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j i : ℂ) *
              pulledGradient g hg U B hB i x := by
  obtain ⟨Q,hdiv',hU',hQ⟩ := graph_scalar_equation g hg u U P F D
    (fun y => (graphDielectric g d y : ℂ)) hU hdiv hP B hB
  refine ⟨Q,hdiv',hU',?_⟩
  intro j
  filter_upwards [hQ j] with x hx
  simpa only [graph_dielectric_pullback] using hx

end OQ14.Packet05GraphBinaryEquation
#print axioms OQ14.Packet05GraphBinaryEquation.graph_binary_scalar_equation

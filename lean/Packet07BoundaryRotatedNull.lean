import Packet07BoundarySwapMeasure

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryRotatedNull
open MeasureTheory Set Packet07BoundaryCoordinates

theorem measurable_chart_graph_null (A : Set Space) (hA : MeasurableSet A)
    (i : Fin 3) (g : Plane → ℝ)
    (hgraph : ∀ x ∈ A, (chart i x).2 = g (chart i x).1) : volume A = 0 := by
  let A' := swap i ⁻¹' A
  have hA' : MeasurableSet A' := hA.preimage (swapCLM i).continuous.measurable
  have hg : ∀ x ∈ A', x 2 = g (ConicalJunctionPhysical.horizontal x) := by
    intro x hx
    have hh := hgraph (swap i x) hx
    simpa only [chart, swap_involution, ConicalJunctionPhysical.split, Prod.fst, Prod.snd] using hh
  have hz := Packet07BoundaryGraphNull.measurable_graph_subset_null A' hA' g hg
  have hp := (Packet07BoundarySwapMeasure.swap_measure_preserving i).measure_preimage hA.nullMeasurableSet
  exact hp.symm.trans hz

end OQ14.Packet07BoundaryRotatedNull
#print axioms OQ14.Packet07BoundaryRotatedNull.measurable_chart_graph_null

import Packet07BoundaryFrontier
import WeakPoynting.Slices

/-! Every measurable subset of an arbitrary vertical graph is volume-null. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07BoundaryGraphNull
open MeasureTheory Set OQ14.ConicalJunctionPhysical
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothCapGraph.Plane

theorem measurable_graph_subset_null (A : Set Space) (hA : MeasurableSet A)
    (g : Plane → ℝ) (hgraph : ∀ x ∈ A, x 2 = g (horizontal x)) : volume A = 0 := by
  let S : Set (FluxSlices.Plane × ℝ) :=
    {p | FluxSlices.split.symm (p.2,p.1) ∈ A}
  have hS : MeasurableSet S := hA.preimage (FluxSlices.split.symm.measurable.comp measurable_swap)
  have hz : (volume : Measure FluxSlices.Plane).prod (volume : Measure ℝ) S = 0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    filter_upwards with q
    have hsub : Prod.mk q ⁻¹' S ⊆ {g ((EuclideanSpace.equiv (Fin 2) ℝ).symm q)} := by
      intro z hz
      have hh := hgraph (FluxSlices.split.symm (z,q)) hz
      have hcoord := FluxSlices.join_coordinates z q
      have hx2 : FluxSlices.split.symm (z,q) 2 = z := by
        have hh2 := congrFun hcoord 2
        simpa using hh2
      have hxy : horizontal (FluxSlices.split.symm (z,q)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm q := by
        ext j
        fin_cases j <;> simp [horizontal, FluxSlices.join_coordinates]
      simp only [mem_singleton_iff]
      simpa only [hx2,hxy] using hh
    exact measure_mono_null hsub (by simp)
  have hs : MeasurePreserving FluxSlices.split (volume : Measure Space)
      ((volume : Measure ℝ).prod (volume : Measure FluxSlices.Plane)) := by
    simpa only [Measure.volume_eq_prod] using FluxSlices.split_measurePreserving
  have hp : MeasurePreserving (fun x : Space => (FluxSlices.transverse x, x 2))
      (volume : Measure Space) ((volume : Measure FluxSlices.Plane).prod (volume : Measure ℝ)) := by
    simpa only [Function.comp_apply, FluxSlices.split_apply, Prod.swap_prod_mk,
      FluxSlices.axis] using
      ((Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure FluxSlices.Plane))).comp hs)
  have hpre := hp.measure_preimage hS.nullMeasurableSet
  have he : (fun x : Space => (FluxSlices.transverse x, x 2)) ⁻¹' S = A := by
    ext x
    change FluxSlices.split.symm (x 2, FluxSlices.transverse x) ∈ A ↔ x ∈ A
    have hx : (x 2, FluxSlices.transverse x) = FluxSlices.split x := by
      rw [FluxSlices.split_apply]
      rfl
    rw [hx, FluxSlices.split.symm_apply_apply]
  rw [he] at hpre
  exact hpre.trans hz

end OQ14.Packet07BoundaryGraphNull
#print axioms OQ14.Packet07BoundaryGraphNull.measurable_graph_subset_null

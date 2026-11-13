import Packet05PhysicalGraphChart
import WeakPoynting.Slices

/-! A continuous graph has three-dimensional volume zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphBoundaryNull
open MeasureTheory OQ14.ConicalJunctionPhysical
open OQ14.Packet05PhysicalGraphChart

theorem continuous_graph_volume_zero (g : Plane → ℝ) (hg : Continuous g) :
    volume {x : Space | x 2 = g (horizontal x)} = 0 := by
  let gP : OQ14.FluxSlices.Plane → ℝ := fun q => g ((EuclideanSpace.equiv (Fin 2) ℝ).symm q)
  have hgP : Continuous gP := hg.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
  let S : Set (OQ14.FluxSlices.Plane × ℝ) := {p | p.2 = gP p.1}
  have hS : MeasurableSet S := (isClosed_eq continuous_snd (hgP.comp continuous_fst)).measurableSet
  have hz : (volume : Measure OQ14.FluxSlices.Plane).prod (volume : Measure ℝ) S = 0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    filter_upwards with q
    have he : Prod.mk q ⁻¹' S = {gP q} := by
      ext x
      simp [S, eq_comm]
    rw [he]
    simp
  have hs : MeasurePreserving OQ14.FluxSlices.split (volume : Measure Space)
      ((volume : Measure ℝ).prod (volume : Measure OQ14.FluxSlices.Plane)) := by
    simpa only [Measure.volume_eq_prod] using OQ14.FluxSlices.split_measurePreserving
  have hp : MeasurePreserving (fun x : Space => (OQ14.FluxSlices.transverse x, x 2))
      (volume : Measure Space) ((volume : Measure OQ14.FluxSlices.Plane).prod (volume : Measure ℝ)) := by
    simpa only [Function.comp_apply, OQ14.FluxSlices.split_apply, Prod.swap_prod_mk,
      OQ14.FluxSlices.axis] using
      ((Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure OQ14.FluxSlices.Plane))).comp
        hs)
  have hpre := hp.measure_preimage hS.nullMeasurableSet
  have he : (fun x : Space => (OQ14.FluxSlices.transverse x, x 2)) ⁻¹' S =
      {x : Space | x 2 = g (horizontal x)} := by
    ext x
    have ht : (EuclideanSpace.equiv (Fin 2) ℝ).symm (OQ14.FluxSlices.transverse x) = horizontal x := by
      ext i
      fin_cases i <;> simp [OQ14.FluxSlices.transverse, horizontal, Fin.succAbove]
    change x 2 = gP (OQ14.FluxSlices.transverse x) ↔ x 2 = g (horizontal x)
    change x 2 = g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (OQ14.FluxSlices.transverse x)) ↔ _
    rw [ht]
  rw [he] at hpre
  exact hpre.trans hz

end OQ14.Packet05GraphBoundaryNull
#print axioms OQ14.Packet05GraphBoundaryNull.continuous_graph_volume_zero

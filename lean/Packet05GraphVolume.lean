import Packet05PhysicalGraphChart
import WeakPoynting.Slices
import Mathlib.MeasureTheory.Group.Prod

/-! The actual graph shear preserves volume even for a merely continuous
height, by translating each vertical fiber and applying Fubini. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphVolume
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap

abbrev ProductPlane := OQ14.FluxSlices.Plane

def graphSplit : Space ≃ᵐ ProductPlane × ℝ :=
  OQ14.FluxSlices.split.trans MeasurableEquiv.prodComm

theorem graphSplit_measurePreserving : MeasurePreserving graphSplit := by
  have hs : MeasurePreserving OQ14.FluxSlices.split (volume : Measure Space)
      ((volume : Measure ℝ).prod (volume : Measure ProductPlane)) := by
    simpa only [Measure.volume_eq_prod] using OQ14.FluxSlices.split_measurePreserving
  have hp := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ProductPlane))).comp hs
  simpa only [graphSplit, MeasurableEquiv.trans_apply,
    Function.comp_apply, Measure.volume_eq_prod] using hp

theorem graph_map_volume_preserving (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (graphMap (liftedHeight g)) := by
  let gp : ProductPlane → ℝ := fun q => g ((EuclideanSpace.equiv (Fin 2) ℝ).symm q)
  have hgp : Continuous gp := hg.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
  let shear : ProductPlane × ℝ → ProductPlane × ℝ := fun p => (p.1, p.2 + gp p.1)
  have hsh : MeasurePreserving shear (volume : Measure (ProductPlane × ℝ)) volume := by
    change MeasurePreserving (fun p : ProductPlane × ℝ => (p.1, p.2 + gp p.1))
      ((volume : Measure ProductPlane).prod (volume : Measure ℝ))
      ((volume : Measure ProductPlane).prod (volume : Measure ℝ))
    have hm : Measurable (Function.uncurry (fun q : ProductPlane => fun z : ℝ => z + gp q)) := by
      exact (continuous_snd.add (hgp.comp continuous_fst)).measurable
    have hv : ∀ᵐ q ∂(volume : Measure ProductPlane), Measure.map (fun z : ℝ => z + gp q) volume = volume := by
      filter_upwards with q
      exact MeasureTheory.map_add_right_eq_self (volume : Measure ℝ) (gp q)
    simpa only [id_eq] using (MeasurePreserving.id (volume : Measure ProductPlane)).skew_product hm hv
  have hmp := (graphSplit_measurePreserving.symm graphSplit).comp (hsh.comp graphSplit_measurePreserving)
  have he (x : Space) : graphSplit (graphMap (liftedHeight g) x) = shear (graphSplit x) := by
    change (OQ14.FluxSlices.transverse (graphMap (liftedHeight g) x),
      graphMap (liftedHeight g) x 2) =
      (OQ14.FluxSlices.transverse x, x 2 + gp (OQ14.FluxSlices.transverse x))
    have ht : OQ14.FluxSlices.transverse (graphMap (liftedHeight g) x) = OQ14.FluxSlices.transverse x := by
      funext j
      fin_cases j <;> simp [graphMap, OQ14.FluxSlices.transverse, OQ14.Maxwell.basis,
        EuclideanSpace.single_apply, PiLp.add_apply, PiLp.smul_apply, Fin.succAbove]
    have hq : (EuclideanSpace.equiv (Fin 2) ℝ).symm (OQ14.FluxSlices.transverse x) = horizontal x := by
      ext j
      fin_cases j <;> simp [OQ14.FluxSlices.transverse, horizontal, Fin.succAbove]
    rw [ht]
    apply Prod.ext
    · rfl
    · change (x + liftedHeight g x • OQ14.Maxwell.basis 2) 2 = x 2 + gp (OQ14.FluxSlices.transverse x)
      change (x + g (horizontal x) • OQ14.Maxwell.basis 2) 2 = x 2 + g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (OQ14.FluxSlices.transverse x))
      rw [hq]
      simp [OQ14.Maxwell.basis, EuclideanSpace.single_apply, PiLp.add_apply, PiLp.smul_apply]
  convert hmp using 1
  funext x
  have h := congrArg graphSplit.symm (he x)
  simpa only [MeasurableEquiv.symm_apply_apply, Function.comp_apply] using h
end OQ14.Packet05GraphVolume
#print axioms OQ14.Packet05GraphVolume.graphSplit_measurePreserving
#print axioms OQ14.Packet05GraphVolume.graph_map_volume_preserving

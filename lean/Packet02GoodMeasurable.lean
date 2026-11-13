import Packet02GoodSet
import Mathlib.MeasureTheory.Integral.Prod
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02GoodMeasurable
open MeasureTheory OQ14.Maxwell OQ14.ModalWeightedMode OQ14.Packet02GoodSet

theorem source_measurable (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (l : Fin 3) :
    Measurable (DynamicVolume.source (coefficient n hn) u l) := by
  unfold DynamicVolume.source
  have hm : Measurable (fun y : Space => u (VectorFourier.coordinateMap y) l) := by
    have h := ((PiLp.proj 2 (fun _ : Fin 3 => ℂ) l : LongitudinalProjection.Vector →L[ℂ] ℂ).continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable u)).measurable
    exact h.comp VectorFourier.coordinateMap.measurable
  exact (Complex.measurable_ofReal.comp
    (((coefficient n hn).measurable.comp VectorFourier.coordinateMap.measurable).sqrt)).mul hm

theorem good_measurable (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) :
    MeasurableSet {x : Space | good n hn u x} := by
  have h (l : Fin 3) : MeasurableSet {x : Space | Integrable (fun y =>
      DynamicVolume.source (coefficient n hn) u l y * inverseSquare (x-y))} := by
    apply measurableSet_integrable
    apply Measurable.stronglyMeasurable
    apply ((source_measurable n hn u l).comp measurable_snd).mul
    unfold inverseSquare
    fun_prop
  simpa only [good, Set.setOf_forall] using MeasurableSet.iInter h

#print axioms OQ14.Packet02GoodMeasurable.source_measurable
#print axioms OQ14.Packet02GoodMeasurable.good_measurable
end OQ14.Packet02GoodMeasurable

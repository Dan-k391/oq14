import Packet07BoundaryGraphNull

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundarySwapMeasure
open MeasureTheory Packet07BoundaryCoordinates

theorem swap_measure_preserving (i : Fin 3) :
    MeasurePreserving (swap i) (volume : Measure Space) volume := by
  have h := (VectorFourier.coordinateMap_preserving.symm).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap i 2)).comp
      VectorFourier.coordinateMap_preserving)
  have he : (fun x : Space => VectorFourier.coordinateMap.symm
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap i 2)) (VectorFourier.coordinateMap x))) = swap i := by
    funext x
    ext j
    simp [VectorFourier.coordinateMap, EuclideanSpace.measurableEquiv, swap,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, Equiv.swap_apply_def]
  exact he ▸ h

end OQ14.Packet07BoundarySwapMeasure
#print axioms OQ14.Packet07BoundarySwapMeasure.swap_measure_preserving

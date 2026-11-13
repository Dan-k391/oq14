import Packet06RoundedIntrinsicPeaks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06VectorPeak
open MeasureTheory OQ14.Maxwell

theorem coordinate_to_vector (F : VectorFourier.VectorL2) (i : Fin 3) (S : Set Maxwell.Space) (M : ℝ)
    (h : 0 < (volume.restrict S) {x | M < ‖NewtonL2.physicalCoordinate F i x‖}) :
    0 < (volume.restrict S) {x | M < ‖F (VectorFourier.coordinateMap x)‖} := by
  apply h.trans_le
  apply measure_mono_ae
  filter_upwards [ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae F i)] with x hx hpeak
  change M < ‖NewtonL2.physicalCoordinate F i x‖ at hpeak
  change M < ‖F (VectorFourier.coordinateMap x)‖
  rw [hx] at hpeak
  exact hpeak.trans_le (PiLp.norm_apply_le (F (VectorFourier.coordinateMap x)) i)
#print axioms OQ14.Packet06VectorPeak.coordinate_to_vector
end OQ14.Packet06VectorPeak

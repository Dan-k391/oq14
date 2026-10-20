import DynamicVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Numerical value of the proved dynamic volume error bound -/

noncomputable section
set_option autoImplicit false

namespace OQ14.DynamicVolume

open MeasureTheory Metric

theorem unitBall_volume :
    (volume : Measure Space).real (ball 0 1) = 4 * Real.pi / 3 := by
  change (volume (ball (0 : Space) 1)).toReal = _
  rw [EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

theorem errorBound_explicit (c : Coefficient) (k R : ℝ) :
    errorBound c k R = 252 * c.bound * k^2 * R^2 := by
  unfold errorBound DynamicConvolution.entryMass
  rw [unitBall_volume]
  field_simp [Real.pi_ne_zero]
  ring

end OQ14.DynamicVolume

#print axioms OQ14.DynamicVolume.unitBall_volume
#print axioms OQ14.DynamicVolume.errorBound_explicit

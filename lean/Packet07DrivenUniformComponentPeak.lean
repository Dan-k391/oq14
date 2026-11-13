import Packet07DrivenUniformAttained

/-! Component peaks from the driven construction are Euclidean-amplitude peaks. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformComponentPeak
open MeasureTheory Set Maxwell Packet05ActualMaximum

theorem component_le_amplitude (E : Field) (i : Fin 3) (x : Space) :
    ‖E x i‖ ≤ physicalAmplitude (fun j y => E y j) x := by
  unfold physicalAmplitude
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg ‖E x j‖))).2
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖E x j‖) (Finset.mem_univ i)

theorem positive_component_peak (E : Field) (K : Set Space) (i : Fin 3) (M : ℝ)
    (h : 0 < (volume.restrict K) {x | M < ‖E x i‖}) :
    0 < (volume.restrict K) {x | M < physicalAmplitude (fun j y => E y j) x} := by
  exact lt_of_lt_of_le h (measure_mono (fun x hx => hx.trans_le (component_le_amplitude E i x)))
end OQ14.Packet07DrivenUniformComponentPeak
#print axioms OQ14.Packet07DrivenUniformComponentPeak.component_le_amplitude
#print axioms OQ14.Packet07DrivenUniformComponentPeak.positive_component_peak

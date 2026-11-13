import Packet06LocalPencil
import ComplexVolumeReciprocity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ExternalKernelReciprocity
open MeasureTheory Metric KernelReciprocity ComplexVolumeReciprocity Packet06LocalPencil

/-- The actual local dyadic Green kernel is reciprocal for arbitrary L²
sources, without requiring either source to be material weighted. -/
theorem kernel_reciprocity (S T : ℝ) (hST : 0 ≤ T+S) (z : ℂ) (F G : VectorFourier.VectorL2) :
    vectorPair (kernel z S T F) G = vectorPair F (kernel z S T G) := by
  have hz : ∀ w, reciprocityDefect F G (kernel w S T) = 0 := by
    apply entire_zero_of_real
    · intro w
      exact ((reciprocityDefect F G).differentiable.comp
        (fun q => (kernel_analyticAt S T hST q).differentiableAt)).analyticAt w
    · intro t
      rw [reciprocityDefect_apply]
      change vectorPair (NewtonL2.newtonOperator F +
        ComplexConvolutionAnalytic.operator (t : ℂ) (T+S) F) G -
        vectorPair F (NewtonL2.newtonOperator G +
        ComplexConvolutionAnalytic.operator (t : ℂ) (T+S) G) = 0
      rw [ComplexConvolutionAnalytic.operator_ofReal]
      rw [vectorPair_add_left,vectorPair_add_right,
        NewtonReciprocity.newton_operator_reciprocity,
        dynamic_operator_reciprocity]
      ring
  exact sub_eq_zero.mp ((reciprocityDefect_apply _ F G).symm.trans (hz z))

/-- The physical incident field paired with the weighted material mode equals
the arbitrary source paired with the actual mode representative on its ball. -/
theorem incident_mode_pairing (c : StaticCoefficient.Coefficient) (S J : ℝ)
    (hSJ : 0 ≤ S+J) (z : ℂ) (f u : VectorFourier.VectorL2) :
    vectorPair (StaticCoefficient.sqrtMultiplier c (kernel z J S f)) u =
      vectorPair f (response c z S J u) := by
  rw [NewtonReciprocity.sqrtMultiplier_reciprocity]
  have h := kernel_reciprocity J S hSJ z f (StaticCoefficient.sqrtMultiplier c u)
  change vectorPair (kernel z J S f) (StaticCoefficient.sqrtMultiplier c u) =
    vectorPair f (kernel z S J (StaticCoefficient.sqrtMultiplier c u))
  simpa only [kernel, add_comm] using h
#print axioms OQ14.Packet06ExternalKernelReciprocity.kernel_reciprocity
#print axioms OQ14.Packet06ExternalKernelReciprocity.incident_mode_pairing
end OQ14.Packet06ExternalKernelReciprocity

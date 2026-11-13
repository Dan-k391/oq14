import Packet06LocalPencil
import Packet06PhysicalPairing
import ModalVolumeNormalization

/-! Physical reciprocal derivative normalization for the actual volume kernel.
The spectral variable does not enter the material coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06PhysicalNormalization
open KernelReciprocity ComplexVolumeReciprocity Packet06LocalPencil
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem volume_derivative (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z =
      -(StaticCoefficient.sqrtMultiplier c * deriv (fun w => kernel w R R) z *
        StaticCoefficient.sqrtMultiplier c) := by
  let S := StaticCoefficient.sqrtMultiplier c
  have hk := (kernel_analyticAt R R (by positivity) z).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_const z (1 : VectorL2 →L[ℂ] VectorL2)).sub
    (((hasDerivAt_const z S).mul hk).mul (hasDerivAt_const z S))
  have he : (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) =
      fun w => 1-S*kernel w R R*S := funext (fun w => weighted_block_eq c w R)
  rw [he]
  simpa only [zero_mul,zero_add,mul_zero,add_zero,zero_sub] using hd.deriv

theorem derivative_pairing (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (u : VectorL2) :
    vectorPair (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) u =
      -vectorPair (deriv (fun w => kernel w R R) z (StaticCoefficient.sqrtMultiplier c u))
        (StaticCoefficient.sqrtMultiplier c u) := by
  rw [volume_derivative c R hR z]
  change pairFunctional u (-(StaticCoefficient.sqrtMultiplier c
    (deriv (fun w => kernel w R R) z (StaticCoefficient.sqrtMultiplier c u)))) = _
  rw [map_neg]
  change -vectorPair (StaticCoefficient.sqrtMultiplier c
    (deriv (fun w => kernel w R R) z (StaticCoefficient.sqrtMultiplier c u))) u = _
  rw [NewtonReciprocity.sqrtMultiplier_reciprocity]

def reciprocalNorm (c : Coefficient) (R : ℝ) (z : ℂ) (u : VectorL2) : ℂ :=
  (z/2) * vectorPair (deriv (fun w => kernel w R R) z (StaticCoefficient.sqrtMultiplier c u))
    (StaticCoefficient.sqrtMultiplier c u)

theorem reciprocalNorm_eq_crossing (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (u : VectorL2) :
    reciprocalNorm c R z u = -(z/2) *
      vectorPair (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) u := by
  rw [derivative_pairing c R hR z]
  unfold reciprocalNorm
  ring

theorem reciprocalNorm_physical (c : Coefficient) (R : ℝ) (z : ℂ) (u : VectorL2) :
    reciprocalNorm c R z u = (z/2) * ∫ x : Maxwell.Space, ∑ i : Fin 3,
      (deriv (fun w => kernel w R R) z (StaticCoefficient.sqrtMultiplier c u))
        (VectorFourier.coordinateMap x) i *
      (StaticCoefficient.sqrtMultiplier c u) (VectorFourier.coordinateMap x) i := by
  unfold reciprocalNorm
  rw [Packet06PhysicalPairing.vectorPair_physical]

theorem reciprocalNorm_nonzero (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : z ≠ 0)
    (u : VectorL2)
    (hd : vectorPair (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) u ≠ 0) :
    reciprocalNorm c R z u ≠ 0 := by
  rw [reciprocalNorm_eq_crossing c R hR z u]
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hz (by norm_num))) hd

theorem source_unit_value (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (u : VectorL2)
    (hu : vectorPair (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) u = 1) :
    reciprocalNorm c R z u = -z/2 := by
  rw [reciprocalNorm_eq_crossing c R hR z u,hu,mul_one,neg_div]

end OQ14.Packet06PhysicalNormalization
#print axioms OQ14.Packet06PhysicalNormalization.volume_derivative
#print axioms OQ14.Packet06PhysicalNormalization.derivative_pairing
#print axioms OQ14.Packet06PhysicalNormalization.reciprocalNorm_eq_crossing
#print axioms OQ14.Packet06PhysicalNormalization.reciprocalNorm_physical
#print axioms OQ14.Packet06PhysicalNormalization.reciprocalNorm_nonzero
#print axioms OQ14.Packet06PhysicalNormalization.source_unit_value

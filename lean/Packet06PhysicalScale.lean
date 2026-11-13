import Packet06PhysicalNormalization

/-! Physical unit reciprocal normalization, distinct from source-unit scaling. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PhysicalScale
open Complex Packet06PhysicalNormalization

theorem reciprocalNorm_scale (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (u : VectorFourier.VectorL2) (a : ℂ) :
    reciprocalNorm c R z (a • u) = a^2 * reciprocalNorm c R z u := by
  rw [reciprocalNorm_eq_crossing c R hR,ModalVolumeNormalization.pairing_rescale,
    reciprocalNorm_eq_crossing c R hR]
  ring

theorem physical_unit_scale (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (u : VectorFourier.VectorL2) (hN : reciprocalNorm c R z u ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ a^2 = (reciprocalNorm c R z u)⁻¹ ∧
      reciprocalNorm c R z (a • u) = 1 := by
  let a := exp (log (reciprocalNorm c R z u)⁻¹/2)
  have ha2 : a^2 = (reciprocalNorm c R z u)⁻¹ := by
    dsimp [a]
    rw [pow_two,←exp_add,show log (reciprocalNorm c R z u)⁻¹/2+
      log (reciprocalNorm c R z u)⁻¹/2=log (reciprocalNorm c R z u)⁻¹ by ring,
      exp_log (inv_ne_zero hN)]
  refine ⟨a,exp_ne_zero _,ha2,?_⟩
  rw [reciprocalNorm_scale c R hR z u a,ha2,inv_mul_cancel₀ hN]

theorem kernel_physical_unit_scale (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : z ≠ 0) (u : VectorFourier.VectorL2) (hu : u ≠ 0)
    (hk : ComplexConvolutionAnalytic.volumeBlock c z R u = 0)
    (hd : KernelReciprocity.vectorPair
      (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) u ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ a • u ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock c z R (a • u) = 0 ∧
      reciprocalNorm c R z (a • u) = 1 := by
  obtain ⟨a,ha,_,hN⟩ := physical_unit_scale c R hR z u (reciprocalNorm_nonzero c R hR z hz u hd)
  exact ⟨a,ha,smul_ne_zero ha hu,by rw [map_smul,hk,smul_zero],hN⟩

end OQ14.Packet06PhysicalScale
#print axioms OQ14.Packet06PhysicalScale.reciprocalNorm_scale
#print axioms OQ14.Packet06PhysicalScale.physical_unit_scale
#print axioms OQ14.Packet06PhysicalScale.kernel_physical_unit_scale

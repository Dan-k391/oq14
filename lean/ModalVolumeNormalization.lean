import ModalVolumeDerivativePairing
import ModalOverlapAngular

/-! Nonzero reciprocal derivative pairing and normalization of the actual
weighted Maxwell residue mode. Kernel simplicity and the full inverse residue
are separate spectral questions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ModalVolumeNormalization
open Complex OQ14.KernelReciprocity OQ14.ComplexVolumeReciprocity
  OQ14.ComplexConvolutionAnalytic OQ14.ModalWeightedMode
  OQ14.ModalAlgebra OQ14.ModalMatching

def derivativeOperator (n : ℝ) (hn : 1 < n) (z : ℂ) :
    VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  deriv (fun w => volumeBlock (coefficient n hn) w 1) z

theorem numerator_pairing_nonzero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) (hs : deriv (tmDet 1 (n : ℂ)) z ≠ 0) :
    vectorPair (derivativeOperator n hn z (ModalVolumeData.numerator n hn z))
      (ModalVolumeData.numerator n hn z) ≠ 0 :=
  (ModalVolumeDerivativePairing.derivative_pairing_nonzero_iff n hn z hz hd hs).mpr
    (ModalOverlapAngular.overlap_nonzero n hn z hz hd)

theorem pairing_rescale (A : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2)
    (u : VectorFourier.VectorL2) (a : ℂ) :
    vectorPair (A (a • u)) (a • u) = a ^ 2 * vectorPair (A u) u := by
  rw [map_smul, vectorPair_smul_left, vectorPair_comm (A u), vectorPair_smul_left,
    vectorPair_comm u (A u)]
  ring

theorem weighted_pairing_nonzero (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (hd : tmDet 1 (n : ℂ) k.val = 0) (hs : deriv (tmDet 1 (n : ℂ)) k.val ≠ 0)
    (f : Amplitudes) (hf : weightedMode n hn k f ≠ 0) :
    vectorPair (derivativeOperator n hn k.val (weightedMode n hn k f))
      (weightedMode n hn k f) ≠ 0 := by
  have he := ModalWeightedResidue.residue_eq_numerator n hn k f
  let a := (residue 1 (n : ℂ) k.val f).1 / I
  have ha : a ≠ 0 := by
    intro hz
    apply hf
    rw [he]
    change a • ModalVolumeData.numerator n hn k.val = 0
    rw [hz, zero_smul]
  rw [he, pairing_rescale]
  exact mul_ne_zero (pow_ne_zero 2 ha) (numerator_pairing_nonzero n hn k.val k.property hd hs)

theorem kernel_left_functional (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : volumeBlock (coefficient n hn) z 1 u = 0)
    (v : VectorFourier.VectorL2) :
    pairFunctional u (volumeBlock (coefficient n hn) z 1 v) = 0 := by
  change vectorPair (volumeBlock (coefficient n hn) z 1 v) u = 0
  rw [volumeBlock_reciprocity _ 1 (by norm_num), hu, vectorPair_comm]
  exact (pairFunctional v).map_zero

theorem exists_normalized_weighted_mode (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (hd : tmDet 1 (n : ℂ) k.val = 0) (hs : deriv (tmDet 1 (n : ℂ)) k.val ≠ 0) :
    ∃ f : Amplitudes, ∃ a : ℂ, a ≠ 0 ∧ a • weightedMode n hn k f ≠ 0 ∧
      volumeBlock (coefficient n hn) k.val 1 (a • weightedMode n hn k f) = 0 ∧
      pairFunctional (a • weightedMode n hn k f) ≠ 0 ∧
      (∀ v, pairFunctional (a • weightedMode n hn k f)
        (volumeBlock (coefficient n hn) k.val 1 v) = 0) ∧
      pairFunctional (a • weightedMode n hn k f)
        (derivativeOperator n hn k.val (a • weightedMode n hn k f)) = 1 := by
  obtain ⟨f, hf, hker⟩ := ModalSphereVolumeKernel.exists_nonzero_weighted_residue n hn k hd hs
  let u := weightedMode n hn k f
  let d := vectorPair (derivativeOperator n hn k.val u) u
  have hd0 : d ≠ 0 := weighted_pairing_nonzero n hn k hd hs f hf
  let a := exp (log d⁻¹ / 2)
  have ha : a ≠ 0 := exp_ne_zero _
  have ha2 : a ^ 2 = d⁻¹ := by
    dsimp only [a]
    rw [pow_two, ← exp_add, show log d⁻¹ / 2 + log d⁻¹ / 2 = log d⁻¹ by ring,
      exp_log (inv_ne_zero hd0)]
  have hunit : pairFunctional (a • u) (derivativeOperator n hn k.val (a • u)) = 1 := by
    change vectorPair (derivativeOperator n hn k.val (a • u)) (a • u) = 1
    rw [pairing_rescale, ha2]
    exact inv_mul_cancel₀ hd0
  have hscaled : volumeBlock (coefficient n hn) k.val 1 (a • u) = 0 := by
    rw [map_smul, hker, smul_zero]
  refine ⟨f, a, ha, smul_ne_zero ha hf, hscaled, ?_,
    kernel_left_functional n hn k.val (a • u) hscaled, hunit⟩
  intro hzero
  have hh := hunit
  rw [hzero, ContinuousLinearMap.zero_apply] at hh
  exact zero_ne_one hh

end OQ14.ModalVolumeNormalization

#print axioms OQ14.ModalVolumeNormalization.numerator_pairing_nonzero
#print axioms OQ14.ModalVolumeNormalization.pairing_rescale
#print axioms OQ14.ModalVolumeNormalization.weighted_pairing_nonzero
#print axioms OQ14.ModalVolumeNormalization.kernel_left_functional
#print axioms OQ14.ModalVolumeNormalization.exists_normalized_weighted_mode

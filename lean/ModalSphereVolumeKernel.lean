import ModalDrivenRepresentation
import ModalWeightedResidue

/-! The actual sphere Maxwell residue belongs to the complex-frequency volume kernel.
Real-frequency representation and analytic continuation are both discharged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalSphereVolumeKernel
open OQ14.ModalAlgebra OQ14.ModalMatching

theorem complex_volume_identity (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
      (ModalVolumeData.numerator n hn z) =
        ModalDipoleOrigin.regularized (n : ℂ) z • ModalVolumeData.incident n hn z := by
  apply ModalVolumeContinuation.complex_identity_of_real n hn
  intro k hk
  exact ModalDrivenRepresentation.volume_equation n hn k hk

theorem numerator_in_kernel (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) :
    ModalVolumeData.numerator n hn z ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
        (ModalVolumeData.numerator n hn z) = 0 := by
  apply ModalVolumeContinuation.nonzero_kernel_of_real_identity n hn
    (fun k hk => ModalDrivenRepresentation.volume_equation n hn k hk) z hz hd

theorem weighted_mode_in_volume_kernel (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (hd : tmDet 1 (n : ℂ) k.val = 0) (f : Amplitudes) :
    ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) k.val 1
      (ModalWeightedMode.weightedMode n hn k f) = 0 :=
  ModalWeightedResidue.residue_in_kernel_of_real_identity n hn
    (fun r hr => ModalDrivenRepresentation.volume_equation n hn r hr) k hd f

theorem exists_nonzero_weighted_residue (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (hd : tmDet 1 (n : ℂ) k.val = 0) (hs : deriv (tmDet 1 (n : ℂ)) k.val ≠ 0) :
    ∃ f : Amplitudes, ModalWeightedMode.weightedMode n hn k f ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) k.val 1
        (ModalWeightedMode.weightedMode n hn k f) = 0 := by
  obtain ⟨f,hf⟩ := ModalWeightedMode.exists_nonzero_weighted_residue n hn k hd hs
  exact ⟨f,hf,weighted_mode_in_volume_kernel n hn k hd f⟩

theorem volumeBlock_not_isUnit (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) :
    ¬ IsUnit (ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1) := by
  intro hunit
  obtain ⟨hu,hker⟩ := numerator_in_kernel n hn z hz hd
  let A := ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
  have hi := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 =>
    L (ModalVolumeData.numerator n hn z)) (Ring.inverse_mul_cancel A hunit)
  change Ring.inverse A (A (ModalVolumeData.numerator n hn z)) = ModalVolumeData.numerator n hn z at hi
  change A (ModalVolumeData.numerator n hn z) = 0 at hker
  rw [hker, map_zero] at hi
  exact hu hi.symm

end OQ14.ModalSphereVolumeKernel

#print axioms OQ14.ModalSphereVolumeKernel.complex_volume_identity
#print axioms OQ14.ModalSphereVolumeKernel.numerator_in_kernel
#print axioms OQ14.ModalSphereVolumeKernel.weighted_mode_in_volume_kernel
#print axioms OQ14.ModalSphereVolumeKernel.exists_nonzero_weighted_residue
#print axioms OQ14.ModalSphereVolumeKernel.volumeBlock_not_isUnit

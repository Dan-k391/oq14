import ModalSphereVolumeKernel
import ComplexVolumeReciprocity

/-! Differentiate the actual sphere volume equation and use physical bilinear
reciprocity. The remaining normalization question is an explicit overlap of
the actual incident and interior numerator fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalVolumeDerivativePairing
open Complex Filter OQ14.ModalVolumeData OQ14.ComplexConvolutionAnalytic
  OQ14.ComplexVolumeReciprocity OQ14.KernelReciprocity
open scoped Topology

theorem regularized_deriv (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    deriv (ModalDipoleOrigin.regularized n) z = deriv (ModalAlgebra.tmDet 1 n) z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact ModalDipoleOrigin.regularized_eq n w hn hw

theorem volume_identity_deriv (n : ℝ) (hn : 1 < n) (z : ℂ) :
    deriv (fun w => volumeBlock (ModalWeightedMode.coefficient n hn) w 1) z
        (numerator n hn z) +
      volumeBlock (ModalWeightedMode.coefficient n hn) z 1 (deriv (numerator n hn) z) =
      deriv (ModalDipoleOrigin.regularized (n : ℂ)) z • incident n hn z +
        ModalDipoleOrigin.regularized (n : ℂ) z • deriv (incident n hn) z := by
  have ha := (volumeBlock_differentiable (ModalWeightedMode.coefficient n hn) 1
    (by norm_num) z).hasDerivAt
  have hu := (numerator_analytic n hn z).differentiableAt.hasDerivAt
  have hd := (ModalDipoleOrigin.regularized_analyticAt (n : ℂ) z).differentiableAt.hasDerivAt
  have hf := (incident_analytic n hn z).differentiableAt.hasDerivAt
  have hl := ha.clm_apply hu
  have hr := hd.smul hf
  have he : (fun w => volumeBlock (ModalWeightedMode.coefficient n hn) w 1
      (numerator n hn w)) =
      fun w => ModalDipoleOrigin.regularized (n : ℂ) w • incident n hn w :=
    funext (ModalSphereVolumeKernel.complex_volume_identity n hn)
  rw [he] at hl
  simpa only [add_comm] using hl.unique hr

theorem derivative_pairing (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    vectorPair
      (deriv (fun w => volumeBlock (ModalWeightedMode.coefficient n hn) w 1) z
        (numerator n hn z)) (numerator n hn z) =
      deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z *
        vectorPair (incident n hn z) (numerator n hn z) := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he := volume_identity_deriv n hn z
  rw [ModalDipoleOrigin.regularized_eq _ _ hn0 hz, hd, zero_smul, add_zero,
    regularized_deriv _ _ hn0 hz] at he
  have hp := congrArg (pairFunctional (numerator n hn z)) he
  change vectorPair (_ + _) (numerator n hn z) = vectorPair (_ • _) (numerator n hn z) at hp
  rw [vectorPair_add_left, volumeBlock_reciprocity _ 1 (by norm_num),
    (ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd).2,
    vectorPair_smul_left] at hp
  have hzero : vectorPair (deriv (numerator n hn) z) 0 = 0 := by
    rw [vectorPair_comm]
    exact (pairFunctional _).map_zero
  simpa only [hzero, add_zero] using hp

theorem derivative_pairing_nonzero_iff (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (hs : deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0) :
    vectorPair
      (deriv (fun w => volumeBlock (ModalWeightedMode.coefficient n hn) w 1) z
        (numerator n hn z)) (numerator n hn z) ≠ 0 ↔
      vectorPair (incident n hn z) (numerator n hn z) ≠ 0 := by
  rw [derivative_pairing n hn z hz hd]
  exact mul_ne_zero_iff_left hs

end OQ14.ModalVolumeDerivativePairing

#print axioms OQ14.ModalVolumeDerivativePairing.regularized_deriv
#print axioms OQ14.ModalVolumeDerivativePairing.volume_identity_deriv
#print axioms OQ14.ModalVolumeDerivativePairing.derivative_pairing
#print axioms OQ14.ModalVolumeDerivativePairing.derivative_pairing_nonzero_iff

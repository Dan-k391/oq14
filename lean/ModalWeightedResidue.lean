import ModalVolumeContinuation

/-! The actual weighted Maxwell residue is a scalar multiple of the entire driven datum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalWeightedResidue
open MeasureTheory OQ14.Maxwell OQ14.ModalMatching OQ14.ModalAlgebra OQ14.ModalOrigin
open scoped Topology

theorem residue_eq_numerator (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (f : Amplitudes) :
    ModalWeightedMode.weightedMode n hn k f =
      ((residue 1 (n : ℂ) k.val f).1/Complex.I) • ModalVolumeData.numerator n hn k.val := by
  apply StaticSphereMaterial.vector_ext_physical
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul ((residue 1 (n : ℂ) k.val f).1/Complex.I)
      (ModalVolumeData.numerator n hn k.val))
  filter_upwards [ModalWeightedMode.weightedMode_actual n hn k f i,
    ModalVolumeData.numerator_actual n hn k.val i, hs] with x hm hu hs
  rw [hs]
  change ModalWeightedMode.weightedMode n hn k f (VectorFourier.coordinateMap x) i =
    ((residue 1 (n : ℂ) k.val f).1/Complex.I) *
      ModalVolumeData.numerator n hn k.val (VectorFourier.coordinateMap x) i
  rw [hm, hu, ModalWeightedMode.coefficient_value]
  by_cases hi : ‖x‖ < 1
  · rw [if_pos hi]
    simp only [ModalPoleMode.electricMode, ModalProfiles.electric, if_pos hi.le,
      entireInnerE, Pi.smul_apply, smul_eq_mul]
    have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    field_simp [hn0]
    ring_nf
    simp [Complex.I_sq]
  · simp [if_neg hi]

theorem residue_in_kernel_of_real_identity (n : ℝ) (hn : 1 < n)
    (hreal : ∀ k : ℝ, 0 < k →
      DynamicVolume.volumeBlock (ModalWeightedMode.coefficient n hn) k 1
        (ModalVolumeData.numerator n hn k) =
        tmDet 1 (n : ℂ) k • ModalVolumeData.incident n hn k)
    (k : ModalShell.Frequency) (hd : tmDet 1 (n : ℂ) k.val = 0) (f : Amplitudes) :
    ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) k.val 1
      (ModalWeightedMode.weightedMode n hn k f) = 0 := by
  rw [residue_eq_numerator, map_smul,
    (ModalVolumeContinuation.nonzero_kernel_of_real_identity n hn hreal k.val k.property hd).2,
    smul_zero]

end OQ14.ModalWeightedResidue

#print axioms OQ14.ModalWeightedResidue.residue_eq_numerator
#print axioms OQ14.ModalWeightedResidue.residue_in_kernel_of_real_identity

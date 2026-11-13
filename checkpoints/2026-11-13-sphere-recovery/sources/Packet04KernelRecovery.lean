import Packet04SliceRecovery
import ModalDipoleSlice
import ComplexKernelResponse

/-! The actual volume-kernel equation and actual dipole numerator vanish
outside the material. Interior angular reconstruction therefore proves
equality in the full physical L² space. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet04KernelRecovery
open Complex MeasureTheory Set OQ14.Maxwell OQ14.Packet04SliceRecovery
  OQ14.ModalVectorAngularSlices

theorem kernel_supported (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) : supportedInUnit u := by
  filter_upwards [ComplexKernelResponse.kernel_coordinate_ae
    (ModalWeightedMode.coefficient n hn) z 1 u hker] with x hx hlarge
  rw [hx, ModalWeightedMode.coefficient_value, if_neg (not_lt.mpr hlarge)]
  simp

theorem numerator_supported (n : ℝ) (hn : 1 < n) (z : ℂ) :
    supportedInUnit (ModalVolumeData.numerator n hn z) := by
  filter_upwards [ModalDipoleSlice.numerator_vector_ae n hn z] with x hx hlarge
  rw [hx, ModalWeightedMode.coefficient_value, if_neg (not_lt.mpr hlarge)]
  simp

theorem kernel_eq_numerator_of_inner_slices (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (c : ℂ)
    (h : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      slice u r = c • slice (ModalVolumeData.numerator n hn z) r) :
    u = c • ModalVolumeData.numerator n hn z := by
  apply eq_of_slices_inside u (c • ModalVolumeData.numerator n hn z)
    (kernel_supported n hn z u hker)
    (supportedInUnit_smul c _ (numerator_supported n hn z))
  filter_upwards [h, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)
    (slice_smul c (ModalVolumeData.numerator n hn z))] with r hr hs
  exact hr.trans hs.symm

end OQ14.Packet04KernelRecovery
#print axioms OQ14.Packet04KernelRecovery.kernel_supported
#print axioms OQ14.Packet04KernelRecovery.numerator_supported
#print axioms OQ14.Packet04KernelRecovery.kernel_eq_numerator_of_inner_slices

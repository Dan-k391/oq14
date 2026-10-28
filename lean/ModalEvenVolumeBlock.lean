import ModalHalfTurnSector
import ModalSphereVolumeKernel

noncomputable section
set_option autoImplicit false
namespace OQ14.ModalEvenVolumeBlock
open OQ14.ModalHalfTurnSector OQ14.ModalWeightedMode OQ14.ModalAlgebra

instance : CompleteSpace evenSector := even_closed.completeSpace_coe

def block (n : ℝ) (hn : 1 < n) (z : ℂ) : evenSector →L[ℂ] evenSector :=
  ((ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1).comp evenSector.subtypeL).codRestrict
    evenSector (fun u => even_invariant n hn z u u.property)

theorem block_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : evenSector) :
    ((block n hn z u : evenSector) : VectorFourier.VectorL2) =
      ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u := rfl

def numerator (n : ℝ) (hn : 1 < n) (z : ℂ) : evenSector :=
  ⟨ModalVolumeData.numerator n hn z, numerator_even n hn z⟩

theorem numerator_kernel (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) :
    numerator n hn z ≠ 0 ∧ block n hn z (numerator n hn z) = 0 := by
  have h := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  constructor
  · intro he
    apply h.1
    exact congrArg Subtype.val he
  · apply Subtype.ext
    exact h.2

theorem block_not_isUnit (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) : ¬ IsUnit (block n hn z) := by
  intro hunit
  obtain ⟨hu,hker⟩ := numerator_kernel n hn z hz hd
  have hi := congrArg (fun L : evenSector →L[ℂ] evenSector => L (numerator n hn z))
    (Ring.inverse_mul_cancel (block n hn z) hunit)
  change Ring.inverse (block n hn z) (block n hn z (numerator n hn z)) = numerator n hn z at hi
  rw [hker, map_zero] at hi
  exact hu hi.symm

#print axioms OQ14.ModalEvenVolumeBlock.block_actual
#print axioms OQ14.ModalEvenVolumeBlock.numerator_kernel
#print axioms OQ14.ModalEvenVolumeBlock.block_not_isUnit
end OQ14.ModalEvenVolumeBlock

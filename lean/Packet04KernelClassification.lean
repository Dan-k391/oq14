import Packet04AxisKernelZero
import Packet04MomentLinearity
import Packet04TMProfiles
import ModalSphereVolumeKernel

/-! Complete actual electric-sector sphere volume-kernel classification.
No radial decomposition, interface trace, outgoing-mode, or abstract
one-dimensional-kernel premise is retained in the final theorems. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04KernelClassification
open Complex MeasureTheory Set MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial

theorem zero_of_axis_radial (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (u : VectorFourier.VectorL2)
    (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (haxis : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (X 2) r = 0) : u = 0 := by
  apply Packet04AxisKernelZero.zero_of_axis_and_nondipoles n hn z hz u hu hker haxis
  intro p l hp hh hl
  exact Packet04TMProfiles.actual_nondipole_radial_zero n hn hna z hz hroot u hker p l hp hh hl

theorem kernel_is_numerator_multiple (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (u : VectorFourier.VectorL2)
    (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    ∃ c : ℂ, u = c • ModalVolumeData.numerator n hn z := by
  let N := ModalVolumeData.numerator n hn z
  obtain ⟨hN0, hNk⟩ := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hroot
  have hNs : N ∈ ModalMeridionalReflection.electricSector :=
    ModalMeridionalReflection.numerator_in_electricSector n hn z
  have hp : (X (2 : Fin 3) : Poly).IsHomogeneous 1 := isHomogeneous_X ℝ 2
  have hh : formalLaplacian (X (2 : Fin 3) : Poly) = 0 := by
    simp [formalLaplacian_apply, Fin.sum_univ_three]
  obtain ⟨a, ha⟩ := ComplexKernelDebye.regular_radial_coefficient n hn z hz u hker (X 2) 1 hp hh
  obtain ⟨b, hb⟩ := ComplexKernelDebye.regular_radial_coefficient n hn z hz N hNk (X 2) 1 hp hh
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hN0
    apply zero_of_axis_radial n hn hna z hz hroot N hNs hNk
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with r hb hr
    have hzrad : (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z N (X 2) r = 0 := by
      simpa only [hb0, zero_mul] using hb
    exact (mul_eq_zero.mp hzrad).resolve_left (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr.1.ne'))
  let c := a/b
  have hvs : u-c • N ∈ ModalMeridionalReflection.electricSector :=
    ModalMeridionalReflection.electricSector.sub_mem hu
      (ModalMeridionalReflection.electricSector.smul_mem c hNs)
  have hvk : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 (u-c • N) = 0 := by
    simp only [map_sub, map_smul, hker, N, hNk, smul_zero, sub_self]
  have hv0 : u-c • N = 0 := by
    apply zero_of_axis_radial n hn hna z hz hroot _ hvs hvk
    filter_upwards [ha, hb, Packet04MomentLinearity.kernel_radial_sub_smul n hn z u N hker hNk c (X 2),
      ae_restrict_mem measurableSet_Ioo] with r ha hb hl hr
    have hrad : (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z (u-c • N) (X 2) r = 0 := by
      calc
        _ = (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u (X 2) r -
            c*((r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z N (X 2) r) := by rw [hl]; ring
        _ = (a-c*b)*RadialOriginSelection.regular 1 (z*n) r := by rw [ha,hb]; ring
        _ = 0 := by simp only [c, div_mul_cancel₀ a hb0, sub_self, zero_mul]
    exact (mul_eq_zero.mp hrad).resolve_left (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr.1.ne'))
  exact ⟨c, sub_eq_zero.mp hv0⟩

theorem kernel_iff_unique_multiple (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (u : VectorFourier.VectorL2) :
    (u ∈ ModalMeridionalReflection.electricSector ∧
      ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) ↔
    ∃! c : ℂ, u = c • ModalVolumeData.numerator n hn z := by
  obtain ⟨hN0,hNk⟩ := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hroot
  constructor
  · rintro ⟨hu,hker⟩
    obtain ⟨c,hc⟩ := kernel_is_numerator_multiple n hn hna z hz hroot u hu hker
    refine ⟨c,hc,?_⟩
    intro d hd
    exact (smul_left_injective ℂ hN0) (hd.symm.trans hc)
  · rintro ⟨c,hc,_⟩
    rw [hc]
    exact ⟨ModalMeridionalReflection.electricSector.smul_mem c
      (ModalMeridionalReflection.numerator_in_electricSector n hn z), by simp only [map_smul,hNk,smul_zero]⟩

def selectedKernel (n : ℝ) (hn : 1 < n) (z : ℂ) : Submodule ℂ VectorFourier.VectorL2 :=
  ModalMeridionalReflection.electricSector ⊓
    LinearMap.ker (ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1).toLinearMap

theorem selectedKernel_eq_span (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    selectedKernel n hn z = Submodule.span ℂ {ModalVolumeData.numerator n hn z} := by
  ext u
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hu
    obtain ⟨c,hc⟩ := kernel_is_numerator_multiple n hn hna z hz hroot u hu.1 hu.2
    exact ⟨c,hc.symm⟩
  · rintro ⟨c,rfl⟩
    exact ⟨ModalMeridionalReflection.electricSector.smul_mem c
      (ModalMeridionalReflection.numerator_in_electricSector n hn z),
      by
        change ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
          (c • ModalVolumeData.numerator n hn z) = 0
        simp only [map_smul, (ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hroot).2, smul_zero]⟩

theorem selectedKernel_finrank (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    Module.finrank ℂ (selectedKernel n hn z) = 1 := by
  rw [selectedKernel_eq_span n hn hna z hz hroot]
  exact finrank_span_singleton (ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hroot).1

end OQ14.Packet04KernelClassification
#print axioms OQ14.Packet04KernelClassification.zero_of_axis_radial
#print axioms OQ14.Packet04KernelClassification.kernel_is_numerator_multiple
#print axioms OQ14.Packet04KernelClassification.kernel_iff_unique_multiple
#print axioms OQ14.Packet04KernelClassification.selectedKernel_eq_span
#print axioms OQ14.Packet04KernelClassification.selectedKernel_finrank

import Packet04KernelZero
import Packet04AxialRecovery
import Packet01Monopole

/-! All actual electric-sector kernel freedom is reduced to the axial
degree-one radial amplitude once the higher physical degrees are excluded. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04AxisKernelZero
open Complex MeasureTheory Set MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.ModalVectorAngularSlices OQ14.Packet04PolynomialCoordinates
  OQ14.Packet04KernelMomentBridge

private theorem sqrtContrast_ne_zero (n : ℝ) (hn : 1 < n) :
    (Real.sqrt (n^2-1) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (ModalWeightedMode.contrast_pos n hn)).ne'

theorem radial_degree_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (hp : p.IsHomogeneous 0) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u p r = 0 := by
  filter_upwards [radial_coordinate_actual n hn z u hker p,
    radial_coordinate_actual n hn z u hker 1,
    Packet01Monopole.monopole_radial_coefficient_eq_zero n hn z hz u hker] with r hp' h1 hm
  have hc : radialCoordinate (slice u r) p = 0 := by
    conv_lhs => rw [degree_zero p hp]
    rw [map_smul, h1, hm, mul_zero, smul_zero]
  exact (mul_eq_zero.mp (hp'.symm.trans hc)).resolve_left (sqrtContrast_ne_zero n hn)

theorem radial_degree_one_of_axis_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (haxis : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (X 2) r = 0)
    (p : Poly) (hp : p.IsHomogeneous 1) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u p r = 0 := by
  have hx (i : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      radialCoordinate (slice u r) (X i) = 0 := by
    have hz : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        ComplexKernelDebye.radialCoefficient n hn z u (X i) r = 0 := by
      by_cases hi : i = 2
      · simpa only [hi] using haxis
      · exact Packet04AxialRecovery.transverse_radial_zero n hn z u hker hu.1 i hi
    filter_upwards [hz, radial_coordinate_actual n hn z u hker (X i)] with r hz ha
    rw [ha, hz, mul_zero]
  filter_upwards [ae_all_iff.mpr hx, radial_coordinate_actual n hn z u hker p] with r hx ha
  have hc : radialCoordinate (slice u r) p = 0 := by
    rw [degree_one_coordinate _ p hp]
    simp only [hx, smul_zero, Finset.sum_const_zero]
  exact (mul_eq_zero.mp (ha.symm.trans hc)).resolve_left (sqrtContrast_ne_zero n hn)

theorem zero_of_axis_and_nondipoles (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2) (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (haxis : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (X 2) r = 0)
    (hother : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous (l+1) → formalLaplacian p = 0 →
      l+1 ≠ 1 → ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        ComplexKernelDebye.radialCoefficient n hn z u p r = 0) : u = 0 := by
  apply Packet04KernelZero.zero_of_radial_moments n hn z hz u hu hker
  intro p l hp hh
  cases l with
  | zero => exact radial_degree_zero n hn z hz u hker p hp
  | succ l =>
    by_cases h1 : l+1 = 1
    · exact radial_degree_one_of_axis_zero n hn z u hu hker haxis p (h1 ▸ hp)
    · exact hother p l hp hh h1

end OQ14.Packet04AxisKernelZero
#print axioms OQ14.Packet04AxisKernelZero.radial_degree_zero
#print axioms OQ14.Packet04AxisKernelZero.radial_degree_one_of_axis_zero
#print axioms OQ14.Packet04AxisKernelZero.zero_of_axis_and_nondipoles

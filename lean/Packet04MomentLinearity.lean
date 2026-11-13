import Packet04KernelMomentBridge

/-! Almost-everywhere linearity of the actual angular slices and kernel
electric radial moments, retaining their physical representative meanings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04MomentLinearity
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.HarmonicPolynomial
  OQ14.ModalVectorAngularSlices OQ14.Packet04PolynomialCoordinates
  OQ14.Packet04KernelMomentBridge OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

theorem slice_sub (u v : VectorFourier.VectorL2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), slice (u-v) r = slice u r - slice v r := by
  have hc := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_sub u v)
  filter_upwards [slice_actual_ae (u-v), slice_actual_ae u, slice_actual_ae v,
    PolarMomentAE.polar_ae hc] with r huv hu hv hc
  apply Lp.ext
  filter_upwards [huv, hu, hv, hc, Lp.coeFn_sub (slice u r) (slice v r)] with ω huv hu hv hc hs
  rw [huv, hc, hs]
  change u (VectorFourier.coordinateMap (r • (ω : Space))) -
    v (VectorFourier.coordinateMap (r • (ω : Space))) = slice u r ω - slice v r ω
  rw [hu, hv]

theorem radial_coordinate_sub (F G : Ambient) (p : Poly) :
    radialCoordinate (F-G) p = radialCoordinate F p - radialCoordinate G p := by
  simp [radialCoordinate, vectorCoordinate, inner_sub_right]

theorem radial_coordinate_smul (c : ℂ) (F : Ambient) (p : Poly) :
    radialCoordinate (c • F) p = c * radialCoordinate F p := by
  simp [radialCoordinate, vectorCoordinate, inner_smul_right]

theorem kernel_radial_sub_smul (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u v : VectorFourier.VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (hv : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 v = 0)
    (c : ℂ) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z (u-c • v) p r =
        ComplexKernelDebye.radialCoefficient n hn z u p r -
          c * ComplexKernelDebye.radialCoefficient n hn z v p r := by
  have hd : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 (u-c • v) = 0 := by
    simp only [map_sub, map_smul, hu, hv, smul_zero, sub_self]
  have hs : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := Ioo_subset_Ioi_self
  filter_upwards [radial_coordinate_actual n hn z (u-c • v) hd p,
    radial_coordinate_actual n hn z u hu p, radial_coordinate_actual n hn z v hv p,
    ae_restrict_of_ae_restrict_of_subset hs (slice_sub u (c • v)),
    ae_restrict_of_ae_restrict_of_subset hs (Packet04SliceRecovery.slice_smul c v)]
    with r hd hu hv hsub hsmul
  rw [hsub, hsmul, radial_coordinate_sub, radial_coordinate_smul, hu, hv] at hd
  have hne : (Real.sqrt (n^2-1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (ModalWeightedMode.contrast_pos n hn)).ne'
  apply mul_left_cancel₀ hne
  linear_combination -hd

end OQ14.Packet04MomentLinearity
#print axioms OQ14.Packet04MomentLinearity.slice_sub
#print axioms OQ14.Packet04MomentLinearity.radial_coordinate_sub
#print axioms OQ14.Packet04MomentLinearity.radial_coordinate_smul
#print axioms OQ14.Packet04MomentLinearity.kernel_radial_sub_smul

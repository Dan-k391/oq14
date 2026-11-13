import Packet04KernelMomentBridge

/-! In the actual electric symmetry sector, all radial moments determine a
volume-kernel vector. Poloidal moments follow from Maxwell; toroidal moments
vanish by the established magnetic chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04KernelZero
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentIntegrability
  OQ14.ModalVectorAngularSlices OQ14.Packet04PolynomialCoordinates
  OQ14.Packet04KernelMomentBridge

theorem poloidal_zero_of_radial_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (hr : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u p r = 0) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      poloidalCoordinate (slice u r) (l+1) p = 0 := by
  have hrad : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      (r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r =
        0 * RadialOriginSelection.regular (l+1) (z*n) r := by
    filter_upwards [hr] with r hr
    simp only [hr, mul_zero, zero_mul]
  have ht := Packet01PoloidalCoefficients.tangential_of_radial n hn z hz u hker p l hp 0 hrad
  filter_upwards [ht, poloidal_coordinate_actual n hn z u hker p l] with r ht ha
  simp only [ht, zero_mul, zero_div, mul_zero] at ha
  exact ha

theorem poloidal_degree_zero (F : ComplexVectorSphere.Ambient) (p : Poly)
    (hp : p.IsHomogeneous 0) : poloidalCoordinate F 0 p = 0 := by
  have hp' := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
  have h : poloidalLinear 0 p = 0 := by
    rw [poloidalLinear_apply]
    ext i
    rw [hp']
    simp [AngularHarmonicEnergy.tangential]
  change vectorCoordinate F (poloidalLinear 0 p) = 0
  rw [h, map_zero]

theorem zero_of_radial_moments (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2) (hu : u ∈ ModalMeridionalReflection.electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (hR : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        ComplexKernelDebye.radialCoefficient n hn z u p r = 0) : u = 0 := by
  have hr (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0) :
      ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), radialCoordinate (slice u r) p = 0 := by
    filter_upwards [radial_coordinate_actual n hn z u hker p, hR p l hp hh] with r ha hr
    rw [ha, hr, mul_zero]
  have hp (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0) :
      ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), poloidalCoordinate (slice u r) l p = 0 := by
    cases l with
    | zero => exact Filter.Eventually.of_forall (fun r => poloidal_degree_zero _ p hp)
    | succ l => exact poloidal_zero_of_radial_zero n hn z hz u hker p l hp (hR p (l+1) hp hh)
  have hzero : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), slice u r = 0 := by
    have hrs := ae_all_iff.mpr (fun a : SphereHarmonicHilbert.TotalIndex =>
      hr _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2))
    have hps := ae_all_iff.mpr (fun a : SphereHarmonicHilbert.TotalIndex =>
      hp _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2))
    have hts := ae_all_iff.mpr (fun a : SphereHarmonicHilbert.TotalIndex =>
      toroidal_coordinate_zero n hn z u hu hker _ _
        (SphereHarmonicBasis.representative_homogeneous a.1 a.2))
    filter_upwards [hrs, hps, hts] with r hr hp ht
    apply Packet04VectorAngular.polynomial_moments_separate
    · exact hr
    · intro a
      change vectorCoordinate (slice u r) (AngularHarmonicEnergy.tangential
        (SphereHarmonicBasis.representative a.1 a.2) a.1) = 0
      rw [← poloidalLinear_apply]
      exact hp a
    · exact ht
  have hs0 : Packet04SliceRecovery.supportedInUnit (0 : VectorFourier.VectorL2) := by
    simpa using Packet04SliceRecovery.supportedInUnit_smul (0 : ℂ) u
      (Packet04KernelRecovery.kernel_supported n hn z u hker)
  apply Packet04SliceRecovery.eq_of_slices_inside u 0
    (Packet04KernelRecovery.kernel_supported n hn z u hker) hs0
  have hz0 : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), slice (0 : VectorFourier.VectorL2) r = 0 := by
    simpa using Packet04SliceRecovery.slice_smul (0 : ℂ) u
  filter_upwards [hzero, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0) hz0] with r hu h0
  exact hu.trans h0.symm

end OQ14.Packet04KernelZero
#print axioms OQ14.Packet04KernelZero.poloidal_zero_of_radial_zero
#print axioms OQ14.Packet04KernelZero.poloidal_degree_zero
#print axioms OQ14.Packet04KernelZero.zero_of_radial_moments

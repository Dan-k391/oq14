import Packet04AxialDipole
import ComplexKernelDebye

/-! The actual weighted-kernel recovery transfers axial symmetry to both
transverse dipole moments of the electric field inside the sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04AxialRecovery
open Complex MeasureTheory Set MvPolynomial OQ14.Maxwell OQ14.AngularPower
  OQ14.ComplexKernelResponse OQ14.Packet04AxialDipole

theorem transverse_radial_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (hax : u ∈ ModalAxialRotation.axialSector) (i : Fin 3) (hi : i ≠ 2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (X i) r = 0 := by
  have hs : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := Ioo_subset_Ioi_self
  have hu := PolarMomentAE.polar_ae
    (kernel_coordinate_ae (ModalWeightedMode.coefficient n hn) z 1 u hker)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hu,
    ae_restrict_of_ae_restrict_of_subset hs (transverse_weighted_moment_zero u hax i hi),
    ae_restrict_mem measurableSet_Ioo] with r hu hm hr
  have he : (∫ ω : Sphere, radialScalar u (r • (ω : Maxwell.Space)) *
      ((ω : Maxwell.Space) i : ℂ) ∂angularMeasure) =
      ((r : ℂ) * (Real.sqrt (n^2-1) : ℂ)) *
        ComplexKernelDebye.radialCoefficient n hn z u (X i) r := by
    rw [ComplexKernelDebye.radialCoefficient, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hu] with ω hω
    have hnorm : ‖r • (ω : Maxwell.Space)‖ = r := by
      simp [norm_smul, sphere_norm, abs_of_pos hr.1]
    rw [ModalWeightedMode.coefficient_value, hnorm, if_pos hr.2] at hω
    unfold radialScalar
    simp only [hω, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      SphericalMomentEquation.angularPolynomial, HarmonicPolynomial.complexEvaluate,
      HarmonicPolynomial.evaluate, eval_X]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnonzero : (r : ℂ) * (Real.sqrt (n^2-1) : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.1.ne')
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (ModalWeightedMode.contrast_pos n hn)).ne')
  exact (mul_eq_zero.mp (he.symm.trans hm)).resolve_left hnonzero

end OQ14.Packet04AxialRecovery
#print axioms OQ14.Packet04AxialRecovery.transverse_radial_zero

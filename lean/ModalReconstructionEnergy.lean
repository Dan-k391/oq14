import ModalAngularIntegratedEnergy
import ModalAngularReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalReconstructionEnergy
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalVolumeAngularCoefficients OQ14.ModalAngularReconstruction
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem reconstruction_energy (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    ‖reconstruct u m‖^2 = ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 *
      ∫ r in Ioi (0 : ℝ), r^2 * ‖coefficient u m r‖^2 := by
  let g := (reconstructedField_memLp u m).toLp (reconstructedField u m)
  let a := ContinuousMap.toLp 2 angularMeasure ℂ m
  have hg : Integrable (fun x : Space => ‖reconstructedField u m x‖^2) :=
    (reconstructedField_memLp u m).norm.integrable_sq
  have hgn : ‖g‖^2 = ∫ x : Space, ‖reconstructedField u m x‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner g g)]
    apply integral_congr_ae
    filter_upwards [(reconstructedField_memLp u m).coeFn_toLp] with x hx
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re, hx]
  have han : ‖a‖^2 = ∫ ω : Sphere, ‖m ω‖^2 ∂angularMeasure := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner a a)]
    apply integral_congr_ae
    filter_upwards [m.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with ω hω
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re, hω]
  have hn : ‖reconstruct u m‖ = ‖g‖ := by
    exact (Lp.compMeasurePreservingₗᵢ ℂ VectorFourier.coordinateMap.symm VectorFourier.coordinateMap_preserving.symm).norm_map g
  rw [hn, hgn, ComplexPolarIntegration.integral_polar _ hg]
  have he : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      r^2 • (∫ ω : Sphere, ‖reconstructedField u m (r • (ω : Space))‖^2 ∂angularMeasure) =
        ‖a‖^2 * (r^2 * ‖coefficient u m r‖^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    have hnorm (ω : Sphere) : ‖r • (ω : Space)‖ = r := by
      simp [norm_smul, sphere_norm, abs_of_pos hrp]
    simp only [reconstructedField, hnorm, ConicalCapField.unit_polar r hrp, norm_smul, mul_pow,
      integral_const_mul, ← han, smul_eq_mul]
    ring
  rw [integral_congr_ae he, integral_const_mul]

theorem reconstruction_bound (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    ‖reconstruct u m‖ ≤ ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 * ‖u‖ := by
  have h := ModalAngularIntegratedEnergy.coefficient_integrated_bound u m
  have he := reconstruction_energy u m
  have hnon : 0 ≤ ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left h hnon
  have hs : ‖reconstruct u m‖^2 ≤
      (‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 * ‖u‖)^2 := by
    rw [he]
    nlinarith [hm]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hnon (norm_nonneg _))).mp hs

#print axioms OQ14.ModalReconstructionEnergy.reconstruction_energy
#print axioms OQ14.ModalReconstructionEnergy.reconstruction_bound
end OQ14.ModalReconstructionEnergy




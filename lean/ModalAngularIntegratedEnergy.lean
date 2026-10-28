import ModalAngularEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalAngularIntegratedEnergy
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalVolumeAngularCoefficients OQ14.ModalVectorAngularSlices
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem coefficient_integrated_bound (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    (∫ r in Ioi (0 : ℝ), r^2 * ‖coefficient u m r‖^2) ≤
      ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 * ‖u‖^2 := by
  let f := physical u
  have hf : Integrable (fun x : Space => ‖f x‖^2) := (Lp.memLp f).norm.integrable_sq
  have hr := ComplexPolarIntegration.integrable_radial_moment _ hf
  have hc := (coefficient_weighted_memLp u m).norm.integrable_sq
  have hc' : IntegrableOn (fun r : ℝ => r^2 * ‖coefficient u m r‖^2) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    convert hc using 1
    funext r
    simp [norm_mul, Complex.norm_real, mul_pow]
  have hp := OQ14.PolarMomentAE.polar_ae (physical_ae u)
  have hb : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      r^2 * ‖coefficient u m r‖^2 ≤
        ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 *
          (r^2 * ∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) := by
    filter_upwards [ModalAngularEnergy.coefficient_pointwise_bound u m, hp] with r h hpr
    have hi : (∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) =
        ∫ ω : Sphere, ‖u (VectorFourier.coordinateMap (r • (ω : Space)))‖^2 ∂angularMeasure := by
      apply integral_congr_ae
      filter_upwards [hpr] with ω hω
      rw [hω]
    rw [hi]
    nlinarith [sq_nonneg r]
  have hn : ‖f‖^2 = ∫ x : Space, ‖f x‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hnorm : ‖f‖ = ‖u‖ := by
    exact (Lp.compMeasurePreservingₗᵢ ℂ VectorFourier.coordinateMap VectorFourier.coordinateMap_preserving).norm_map u
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 *
          (r^2 * ∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) :=
      integral_mono_ae hc' (by simpa [smul_eq_mul] using hr.const_mul _) hb
    _ = _ := by
      rw [integral_const_mul]
      have hh := ComplexPolarIntegration.integral_polar (fun x : Space => ‖f x‖^2) hf
      simp only [smul_eq_mul] at hh
      rw [← hh, ← hn, hnorm]

#print axioms OQ14.ModalAngularIntegratedEnergy.coefficient_integrated_bound
end OQ14.ModalAngularIntegratedEnergy


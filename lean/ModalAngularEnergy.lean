import ModalAngularSlicePairing
import L2Parametric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OQ14.ModalAngularEnergy
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalVolumeAngularCoefficients OQ14.ModalVectorAngularSlices
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem coefficient_pointwise_bound (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ‖coefficient u m r‖^2 ≤
      ‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2 *
        ∫ ω : Sphere, ‖u (VectorFourier.coordinateMap (r • (ω : Space)))‖^2 ∂angularMeasure := by
  filter_upwards [ModalAngularSlicePairing.coefficient_slice_inner u m, slice_actual_ae u] with r hc hs
  have hn : ‖slice u r‖^2 = ∫ ω : Sphere,
      ‖u (VectorFourier.coordinateMap (r • (ω : Space)))‖^2 ∂angularMeasure := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (slice u r) (slice u r))]
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re, hω]
  have hi := norm_inner_le_norm (𝕜 := ℂ) (ContinuousMap.toLp 2 angularMeasure ℂ m) (slice u r)
  rw [← hc] at hi
  calc
    _ ≤ (‖ContinuousMap.toLp 2 angularMeasure ℂ m‖ * ‖slice u r‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = _ := by rw [mul_pow,hn]

#print axioms OQ14.ModalAngularEnergy.coefficient_pointwise_bound
end OQ14.ModalAngularEnergy


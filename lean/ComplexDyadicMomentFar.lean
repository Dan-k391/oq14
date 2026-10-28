import ComplexDyadicOutgoing
import SphericalMomentEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexDyadicMomentFar
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.ComplexDyadicOutgoing
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.AngularPower
open scoped Topology InnerProductSpace

def scale (z : ℂ) (r : ℝ) : ℂ := (r : ℂ) * Complex.exp (-I*z*r)

def momentAmplitude (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (p : Poly) (i : Fin 3) : ℂ := ∫ ω : Sphere, amplitude c z u ω i * angularPolynomial p ω ∂angularMeasure

theorem scaled_field_bound (c : StaticCoefficient.Coefficient) (z : ℂ) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 2*R < r) (hr2 : 2 ≤ r) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    ‖scale z r * ComplexExteriorIntegral.field c z u (r • n) i‖ ≤
      ((2 * Real.exp (‖z‖*R) / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1))) *
        (∑ j : Fin 3, ∫ y, ‖DynamicVolume.source c u j y‖) := by
  let C := (2 * Real.exp (‖z‖*R) / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hnorm : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hx : R < ‖r • n‖ := by rw [hnorm]; linarith
  simp only [ComplexExteriorIntegral.field, scale, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hρ := DynamicVolume.source_integrable c u R hc j
  have hz := DynamicVolume.source_zero c u R hc j
  have hi := NewtonExteriorResponse.source_integrand_integrable
    (fun x => ComplexDynamicKernel.dyadic z x i j) (DynamicVolume.source c u j)
    (fun x hx => ComplexExteriorIntegral.dyadic_continuousAt z i j x hx) hρ R hz (r • n) hx
  rw [← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  have hm : Integrable (fun y => ‖(r : ℂ) * Complex.exp (-I*z*r) *
      (DynamicVolume.source c u j y * ComplexDynamicKernel.dyadic z (r • n-y) i j)‖) :=
    (hi.const_mul _).norm
  have hb : Integrable (fun y => C * ‖DynamicVolume.source c u j y‖) := hρ.norm.const_mul C
  have hpoint : ∀ᵐ y : Space, ‖(r : ℂ) * Complex.exp (-I*z*r) *
      (DynamicVolume.source c u j y * ComplexDynamicKernel.dyadic z (r • n-y) i j)‖ ≤
      C * ‖DynamicVolume.source c u j y‖ := by
    filter_upwards with y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · have he : (r : ℂ) * Complex.exp (-I*z*r) *
          (DynamicVolume.source c u j y * ComplexDynamicKernel.dyadic z (r • n-y) i j) =
          DynamicVolume.source c u j y * ((r : ℂ) * Complex.exp (-I*z*r) *
            ComplexDynamicKernel.dyadic z (r • n-y) i j) := by ring
      rw [he, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (scaled_dyadic_bound z R r hR hr hr2 n y hn hy i j) (norm_nonneg _)
    · simp [hz y hy]
  exact (integral_mono_ae hm hb hpoint).trans_eq (by rw [integral_const_mul])

theorem scaled_moment_limit (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Poly) (i : Fin 3) :
    Tendsto (fun r : ℝ => scale z r * RadialMoment.moment
      (fun x => ComplexExteriorIntegral.field c z u x i) (angularPolynomial p) r) atTop
      (𝓝 (momentAmplitude c z u p i)) := by
  have he (r : ℝ) : scale z r * RadialMoment.moment
      (fun x => ComplexExteriorIntegral.field c z u x i) (angularPolynomial p) r =
      ∫ ω : Sphere, (scale z r * ComplexExteriorIntegral.field c z u (r • (ω : Space)) i) *
        angularPolynomial p ω ∂angularMeasure := by
    unfold RadialMoment.moment
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  simp_rw [he]
  let C := ((2 * Real.exp (‖z‖*R) / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1))) *
        (∑ j : Fin 3, ∫ y, ‖DynamicVolume.source c u j y‖)
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun ω : Sphere => C * ‖angularPolynomial p ω‖)
  · filter_upwards [eventually_gt_atTop (2*R)] with r hr
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
    have hcont : Continuous (fun ω : Sphere => ComplexExteriorIntegral.field c z u (r • (ω : Space)) i) := by
      apply continuous_iff_continuousAt.mpr
      intro ω
      have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr0]
      have hm : Continuous (fun ω : Sphere => r • (ω : Space)) := continuous_const.smul continuous_subtype_val
      have hfield : ContinuousAt (fun ω : Sphere => ComplexExteriorIntegral.field c z u (r • (ω : Space))) ω := 
        (ComplexExteriorIntegral.field_continuousAt c z R u hc (r • (ω : Space))
          (by rw [hnorm]; linarith)).comp (f := fun ω : Sphere => r • (ω : Space)) hm.continuousAt
      exact (continuous_apply i).continuousAt.comp (f := fun ω : Sphere => ComplexExteriorIntegral.field c z u (r • (ω : Space))) hfield
    exact (((continuous_const.mul hcont).mul (angularPolynomial_continuous p)).aestronglyMeasurable)
  · filter_upwards [eventually_gt_atTop (2*R), eventually_ge_atTop (2 : ℝ)] with r hr hr2
    filter_upwards with ω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (scaled_field_bound c z R r hR hr hr2 u hc ω (sphere_norm ω) i) (norm_nonneg _)
  · exact ((angularPolynomial_continuous p).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul C
  · filter_upwards with ω
    exact (field_far_limit c z R hR u hc ω (sphere_norm ω) i).mul_const _

#print axioms OQ14.ComplexDyadicMomentFar.scaled_moment_limit
#print axioms OQ14.ComplexDyadicMomentFar.scaled_field_bound
end OQ14.ComplexDyadicMomentFar






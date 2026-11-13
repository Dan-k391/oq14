import Packet06GradientOutgoing
import Packet06GlobalMaxwell

/-! Outgoing far-field limits of the actual complex magnetic convolution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06MagneticOutgoing
open Complex MeasureTheory Metric Filter Maxwell ComplexGreenKernel Packet06GradientOutgoing
open scoped Topology InnerProductSpace

theorem gradient_response_limit (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-I*z*r)*
      KernelConvolution.response (fun x => phiGradient z x i) ρ (r • n)) atTop
      (𝓝 (ComplexScalarFar.amplitude z ρ n * (I*z*GreenKernel.unitCoordinate i n))) := by
  have hlim : Tendsto (fun r : ℝ => ∫ y, ρ y*((r : ℂ)*Complex.exp (-I*z*r)*phiGradient z (r • n-y) i))
      atTop (𝓝 (∫ y, ρ y*((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ))/(4*Real.pi)) * (I*z*GreenKernel.unitCoordinate i n)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun y => ‖ρ y‖*((2*Real.exp (‖z‖*R)/(4*Real.pi))*(‖z‖+1)))
    · apply Eventually.of_forall
      intro r
      exact hρ.aestronglyMeasurable.mul
        (((ComplexMagneticLocal.gradient_measurable z i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.const_mul _)
    · filter_upwards [eventually_gt_atTop (2*R),eventually_ge_atTop (2 : ℝ)] with r hr hr2
      filter_upwards with y
      by_cases hy : y ∈ closedBall (0 : Space) R
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (scaled_gradient_bound z R r hR hr hr2 n y hn hy i) (norm_nonneg _)
      · simp [hc y hy]
    · exact hρ.norm.mul_const _
    · filter_upwards with y
      exact tendsto_const_nhds.mul (scaled_gradient_limit z n y hn i)
  have htarget : (∫ y, ρ y*((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ))/(4*Real.pi)) * (I*z*GreenKernel.unitCoordinate i n))) =
      ComplexScalarFar.amplitude z ρ n * (I*z*GreenKernel.unitCoordinate i n) := by
    rw [ComplexScalarFar.amplitude,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards with r
  rw [KernelConvolution.response,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

def amplitude (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (n : Space) (i : Fin 3) : ℂ :=
  z^2 * (GreenKernel.unitCoordinate (WeakCurl.next i) n * ComplexScalarFar.amplitude z (DynamicVolume.source c u (WeakCurl.previous i)) n -
    GreenKernel.unitCoordinate (WeakCurl.previous i) n * ComplexScalarFar.amplitude z (DynamicVolume.source c u (WeakCurl.next i)) n)

theorem magnetic_outgoing (c : StaticCoefficient.Coefficient) (z : ℂ) (S : ℝ) (hS : 0 ≤ S)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-I*z*r)*ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) (r • n) i)
      atTop (𝓝 (amplitude c z u n i)) := by
  have h1 := gradient_response_limit z S hS (DynamicVolume.source c u (WeakCurl.previous i))
    (DynamicVolume.source_integrable c u S hc _) (DynamicVolume.source_zero c u S hc _) n hn (WeakCurl.next i)
  have h2 := gradient_response_limit z S hS (DynamicVolume.source c u (WeakCurl.next i))
    (DynamicVolume.source_integrable c u S hc _) (DynamicVolume.source_zero c u S hc _) n hn (WeakCurl.previous i)
  have h := (h1.sub h2).const_mul (-(I*z))
  have he : -(I*z) *
      (ComplexScalarFar.amplitude z (DynamicVolume.source c u (WeakCurl.previous i)) n * (I*z*GreenKernel.unitCoordinate (WeakCurl.next i) n) -
        ComplexScalarFar.amplitude z (DynamicVolume.source c u (WeakCurl.next i)) n * (I*z*GreenKernel.unitCoordinate (WeakCurl.previous i) n)) =
      amplitude c z u n i := by
    unfold amplitude
    ring_nf
    simp [Complex.I_sq,sub_eq_add_neg]
  rw [he] at h
  apply h.congr'
  filter_upwards with r
  unfold ComplexMagneticLocal.magnetic
  ring

end OQ14.Packet06MagneticOutgoing
#print axioms OQ14.Packet06MagneticOutgoing.gradient_response_limit
#print axioms OQ14.Packet06MagneticOutgoing.magnetic_outgoing

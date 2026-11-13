import ComplexDyadicOutgoing
import ComplexMagneticLocal

/-! Complex-frequency outgoing gradient kernel limits and uniform source bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06GradientOutgoing
open Complex MeasureTheory Metric Filter Maxwell ComplexGreenKernel
open scoped Topology InnerProductSpace

theorem gradient_factorization (z : ℂ) (x : Space) (i : Fin 3) :
    phiGradient z x i = phi z x * (I*z-(‖x‖ : ℂ)⁻¹) * GreenKernel.unitCoordinate i x := by
  unfold phiGradient phi radialD radial GreenKernel.unitCoordinate
  push_cast
  simp only [div_eq_mul_inv,inv_pow]
  ring

theorem unitCoordinate_limit (n y : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => GreenKernel.unitCoordinate i (r • n-y)) atTop
      (𝓝 (GreenKernel.unitCoordinate i n)) := by
  have hi := tendsto_inv_atTop_zero.comp (ComplexDyadicOutgoing.ray_distance_tendsto n y hn)
  have hb : Tendsto (fun r : ℝ => (2*‖y‖)*‖r • n-y‖⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hi.const_mul (2*‖y‖)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_gt_atTop ‖y‖,eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hx : r • n ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simp [norm_smul,hn,abs_of_pos hr0,hr0.ne']
  have hz : r • n-y ≠ 0 := by
    intro he
    have hh := norm_sub_norm_le (r • n) y
    rw [he,norm_zero] at hh
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hn,mul_one] at hh
    linarith
  have h := ScalarRadiation.unitCoordinate_difference i (r • n) (r • n-y) hx hz
  have he := congrFun (MaxwellFarField.ray_direction n hn r hr0) i
  change GreenKernel.unitCoordinate i (r • n) = GreenKernel.unitCoordinate i n at he
  rw [he,show r • n-y-r • n = -y by abel,norm_neg] at h
  simpa only [div_eq_mul_inv,norm_norm] using h

theorem scaled_gradient_limit (z : ℂ) (n y : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-I*z*r)*phiGradient z (r • n-y) i)
      atTop (𝓝 ((Complex.exp (-I*z*(⟪n,y⟫_ℝ : ℝ))/(4*Real.pi)) * (I*z*GreenKernel.unitCoordinate i n))) := by
  have hi : Tendsto (fun r : ℝ => ((‖r • n-y‖ : ℝ) : ℂ)⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (ComplexDyadicOutgoing.ray_distance_tendsto n y hn))
    simpa only [Function.comp_def,ofReal_inv,ofReal_zero] using h
  have h := (ComplexScalarFar.scaledKernel_limit z n y hn).mul
    (((tendsto_const_nhds : Tendsto (fun _ : ℝ => I*z) atTop (𝓝 (I*z))).sub hi).mul
      (unitCoordinate_limit n y hn i))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with r
  rw [gradient_factorization]
  dsimp only [ComplexScalarFar.scaledKernel]
  ring

theorem scaled_gradient_bound (z : ℂ) (R r : ℝ) (hR : 0 ≤ R) (hr : 2*R < r) (hr2 : 2 ≤ r)
    (n y : Space) (hn : ‖n‖ = 1) (hy : y ∈ closedBall 0 R) (i : Fin 3) :
    ‖(r : ℂ)*Complex.exp (-I*z*r)*phiGradient z (r • n-y) i‖ ≤
      (2*Real.exp (‖z‖*R)/(4*Real.pi))*(‖z‖+1) := by
  have hr0 : 0 < r := by linarith
  have hnr : ‖r • n‖ = r := by simp [norm_smul,hn,abs_of_pos hr0]
  have hd := (ScalarRadiation.distance_lower_bound R hR (r • n) y (by rwa [hnr]) hy).2.2
  rw [hnr] at hd
  have hd1 : 1 ≤ ‖r • n-y‖ := by linarith
  have hi : ‖r • n-y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
  have hfactor : ‖I*z-(‖r • n-y‖ : ℂ)⁻¹‖ ≤ ‖z‖+1 := by
    have hh := norm_sub_le (I*z) (‖r • n-y‖ : ℂ)⁻¹
    simp only [norm_mul,norm_I,one_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm] at hh
    linarith
  have he : (r : ℂ)*Complex.exp (-I*z*r)*phiGradient z (r • n-y) i =
      ComplexScalarFar.scaledKernel z r n y * (I*z-(‖r • n-y‖ : ℂ)⁻¹) * GreenKernel.unitCoordinate i (r • n-y) := by
    rw [gradient_factorization]
    dsimp only [ComplexScalarFar.scaledKernel]
    ring
  rw [he,norm_mul,norm_mul]
  have h1 := mul_le_mul (ComplexScalarFar.scaledKernel_bound z R r hR hr n y hn hy) hfactor
    (norm_nonneg _) (by positivity : 0 ≤ 2*Real.exp (‖z‖*R)/(4*Real.pi))
  have h2 := mul_le_mul h1 (ScalarRadiation.unitCoordinate_norm_le i (r • n-y))
    (norm_nonneg _) (by positivity : 0 ≤ (2*Real.exp (‖z‖*R)/(4*Real.pi))*(‖z‖+1))
  simpa only [mul_one] using h2

end OQ14.Packet06GradientOutgoing
#print axioms OQ14.Packet06GradientOutgoing.gradient_factorization
#print axioms OQ14.Packet06GradientOutgoing.unitCoordinate_limit
#print axioms OQ14.Packet06GradientOutgoing.scaled_gradient_limit
#print axioms OQ14.Packet06GradientOutgoing.scaled_gradient_bound

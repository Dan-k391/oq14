import SourceHerglotzWhole
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Derived gap-scaled whole-plane coherent constants vanish with small source errors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzScaling
open MeasureTheory Metric Set Filter SourceHerglotzWhole
open scoped Topology

theorem electric_scaled_limit (k R T γ : ℝ) (hγ : γ ≠ 0) :
    Tendsto (fun a : ℝ => electricConstant k R T (γ*a)*a^2) (𝓝[>] 0) (𝓝 0) := by
  let L := 2*SphereReactionKernel.entryBound k*PlaneMaxwellLocal.electricCoefficient k R T*
    (Real.pi+PlaneInverseCube.diskConstant)/γ
  have he : (fun a : ℝ => electricConstant k R T (γ*a)*a^2) =ᶠ[𝓝[>] 0]
      (fun a => L*a+tailConstant k R T*a^2) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hna : a ≠ 0 := ne_of_gt ha
    unfold electricConstant L
    field_simp [hγ, hna]
    ring
  apply Tendsto.congr' he.symm
  have ht : Continuous (fun a : ℝ => L*a+tailConstant k R T*a^2) := by fun_prop
  simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
    (ht.continuousAt (x := 0)).tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

theorem logarithm_scaled_limit (M γ : ℝ) (hM : M ≠ 0) (hγ : γ ≠ 0) :
    Tendsto (fun a : ℝ => a^2*Real.log (M/(γ*a))) (𝓝[>] 0) (𝓝 0) := by
  have he : (fun a : ℝ => a^2*Real.log (M/(γ*a))) =ᶠ[𝓝[>] 0]
      (fun a => (Real.log M-Real.log γ)*a^2-a*(a*Real.log a)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hna : a ≠ 0 := ne_of_gt ha
    rw [Real.log_div hM (mul_ne_zero hγ hna), Real.log_mul hγ hna]
    ring
  apply Tendsto.congr' he.symm
  have ht : Continuous (fun a : ℝ => (Real.log M-Real.log γ)*a^2-a*(a*Real.log a)) :=
    (continuous_const.mul (continuous_id.pow 2)).sub (continuous_id.mul Real.continuous_mul_log)
  simpa only [zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using
    (ht.continuousAt (x := 0)).tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

theorem magnetic_scaled_limit (k R T γ : ℝ) (hM : T+R ≠ 0) (hγ : γ ≠ 0) :
    Tendsto (fun a : ℝ => magneticConstant k R T (γ*a)*a^2) (𝓝[>] 0) (𝓝 0) := by
  let C := 4*SphereReactionKernel.entryBound k*|k| * (4*Real.pi)⁻¹
  let B := |k| * (2*Real.pi*(T+R))+Real.pi
  have hpoly : Tendsto (fun a : ℝ => a^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((show Continuous (fun a : ℝ => a^2) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlog := logarithm_scaled_limit (T+R) γ hM hγ
  have ht := ((hpoly.const_mul B).add (hlog.const_mul PlaneInverseCube.diskConstant)).const_mul C
  have hu := ht.add (hpoly.const_mul (tailConstant k R T))
  convert hu using 1
  · funext a
    unfold magneticConstant PlaneMaxwellSharp.gradientMass C B
    ring
  · simp

end OQ14.SourceHerglotzScaling
#print axioms OQ14.SourceHerglotzScaling.electric_scaled_limit
#print axioms OQ14.SourceHerglotzScaling.logarithm_scaled_limit
#print axioms OQ14.SourceHerglotzScaling.magnetic_scaled_limit

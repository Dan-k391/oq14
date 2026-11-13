import Packet06ActualAngularBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeUniformSeries
open Filter Set OQ14.CapLegendreSeries
open scoped Topology

theorem powerSum_uniform_bound (c : ℕ → ℝ) (C ρ w : ℝ) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hw : |w| ≤ ρ)
    (hc : ∀ n, |c n| ≤ C * (n+1 : ℝ)) :
    |powerSum c w| ≤ ∑' n : ℕ, C * (n+1 : ℝ) * ρ^n := by
  have hρabs : |w| < 1 := lt_of_le_of_lt hw hρ1
  have hs := power_summable_growth c C 1 (by simpa using hc) w hρabs
  have hmajor : Summable (fun n : ℕ => C*(n+1 : ℝ)*ρ^n) := by
    have h := (geometric_succ_summable 1 ρ hρ hρ1).mul_left C
    simpa only [pow_one,mul_assoc] using h
  have hterm (n : ℕ) : ‖c n * w^n‖ ≤ C*(n+1 : ℝ)*ρ^n := by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_pow]
    exact mul_le_mul (hc n) (pow_le_pow_left₀ (abs_nonneg _) hw _) (pow_nonneg (abs_nonneg _) _) (by positivity)
  calc
    |powerSum c w| = ‖∑' n, c n*w^n‖ := by simp [powerSum,Real.norm_eq_abs]
    _ ≤ ∑' n, ‖c n*w^n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, C*(n+1 : ℝ)*ρ^n := (hs.norm).tsum_le_tsum hterm hmajor
#print axioms OQ14.Packet06ConeUniformSeries.powerSum_uniform_bound
end OQ14.Packet06ConeUniformSeries

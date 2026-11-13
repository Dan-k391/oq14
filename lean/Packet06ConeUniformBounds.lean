import Packet06ConeUniformSeries
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeUniformBounds
open Filter Set OQ14.CapLegendreSeries
open scoped Topology

def majorant (ρ : ℝ) : ℝ := ∑' n : ℕ, 2 * (n+1 : ℝ) * ρ^n

theorem majorant_nonnegative (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ majorant ρ := by
  apply tsum_nonneg
  intro n
  positivity

theorem pole_bound (a z ρ : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : |(1-z)/2| ≤ ρ) : |pole a z| ≤ majorant ρ := by
  apply Packet06ConeUniformSeries.powerSum_uniform_bound _ 2 ρ _ (by norm_num) hρ hρ1 hz
  intro n
  have h := poleCoeff_bound a ha n
  have hn : (1 : ℝ) ≤ n+1 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  nlinarith

theorem poleD_bound (a z ρ : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : |(1-z)/2| ≤ ρ) : |poleD a z| ≤ majorant ρ := by
  have h := Packet06ConeUniformSeries.powerSum_uniform_bound (derivativeCoeff (poleCoeff a)) 2 ρ _
    (by norm_num) hρ hρ1 hz (by
      intro n
      have hh := derivativeCoeff_growth (poleCoeff a) 2 (by norm_num) 0 (poleCoeff_growth a ha) n
      simpa using hh)
  change |powerSum (derivativeCoeff (poleCoeff a)) ((1-z)/2)| ≤ majorant ρ at h
  have hm := majorant_nonnegative ρ hρ.le
  unfold poleD
  rw [abs_mul,abs_of_nonpos (by norm_num : (-1/2 : ℝ) ≤ 0)]
  norm_num only [neg_div,neg_neg] at *
  change (1/2 : ℝ)*|powerSum (derivativeCoeff (poleCoeff a)) ((1-z)/2)| ≤ majorant ρ
  nlinarith

theorem odd_bound (a z ρ : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : |z| ≤ 1) (hzρ : |z^2| ≤ ρ) : |odd a z| ≤ majorant ρ := by
  have h := Packet06ConeUniformSeries.powerSum_uniform_bound (oddCoeff a) 2 ρ _
    (by norm_num) hρ hρ1 hzρ (by
      intro n
      have hh := oddCoeff_bound a ha n
      rw [abs_of_nonneg hh.1]
      have hn : (1 : ℝ) ≤ n+1 := by
        have h := Nat.cast_nonneg (α := ℝ) n
        linarith
      nlinarith)
  have hm := majorant_nonnegative ρ hρ.le
  unfold odd
  rw [abs_mul]
  change |powerSum (oddCoeff a) (z^2)| ≤ majorant ρ at h
  have hh := mul_le_mul hz h (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [one_mul] using hh

theorem oddD_bound (a z ρ : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hz : |z| ≤ 1) (hzρ : |z^2| ≤ ρ) : |oddD a z| ≤ 3*majorant ρ := by
  have h1 := Packet06ConeUniformSeries.powerSum_uniform_bound (oddCoeff a) 2 ρ _
    (by norm_num) hρ hρ1 hzρ (by
      intro n
      have hh := oddCoeff_bound a ha n
      rw [abs_of_nonneg hh.1]
      have hn : (1 : ℝ) ≤ n+1 := by
        have h := Nat.cast_nonneg (α := ℝ) n
        linarith
      nlinarith)
  have h2 := Packet06ConeUniformSeries.powerSum_uniform_bound (derivativeCoeff (oddCoeff a)) 2 ρ _
    (by norm_num) hρ hρ1 hzρ (by
      intro n
      have hh := derivativeCoeff_growth (oddCoeff a) 1 (by norm_num) 0 (oddCoeff_growth a ha) n
      have hn : 0 ≤ (n+1 : ℝ) := by positivity
      norm_num only [pow_zero,mul_one,zero_add,pow_one] at hh
      nlinarith)
  change |powerSum (oddCoeff a) (z^2)| ≤ majorant ρ at h1
  change |powerSum (derivativeCoeff (oddCoeff a)) (z^2)| ≤ majorant ρ at h2
  have hz2 : |z^2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg z]
  have hm := majorant_nonnegative ρ hρ.le
  unfold oddD
  calc
    _ ≤ |powerSum (oddCoeff a) (z^2)| + |2*z^2*powerSum (derivativeCoeff (oddCoeff a)) (z^2)| := abs_add _ _
    _ ≤ majorant ρ + 2*majorant ρ := by
      apply add_le_add h1
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have hp := mul_le_mul hz2 h2 (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
      simp only [one_mul] at hp
      linarith
    _ = _ := by ring
#print axioms OQ14.Packet06ConeUniformBounds.majorant_nonnegative
#print axioms OQ14.Packet06ConeUniformBounds.pole_bound
#print axioms OQ14.Packet06ConeUniformBounds.poleD_bound
#print axioms OQ14.Packet06ConeUniformBounds.odd_bound
#print axioms OQ14.Packet06ConeUniformBounds.oddD_bound
end OQ14.Packet06ConeUniformBounds

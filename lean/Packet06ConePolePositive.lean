import Packet06ConeFieldLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConePolePositive
open Filter Set OQ14.CapLegendreSeries
open scoped Topology

theorem pole_positive_near_north (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hz0 : (1/2 : ℝ) ≤ z) (hz1 : z ≤ 1) : 0 < pole a z := by
  let w : ℝ := (1-z)/2
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have hw1 : w ≤ 1/4 := by dsimp [w]; linarith
  have hwabs : |w| < 1 := by rw [abs_of_nonneg hw0]; linarith
  have hs : Summable (fun n => poleCoeff a n * w^n) := power_summable _ 2 (poleCoeff_bound a ha) w hwabs
  have htail : Summable (fun n => poleCoeff a (n+1) * w^(n+1)) := hs.comp_injective Nat.succ_injective
  have hg : Summable (fun n : ℕ => 2*w^(n+1)) := by
    have h := (summable_geometric_of_abs_lt_one hwabs).mul_left (2*w)
    convert h using 1
    ext n
    simp only [pow_succ]
    ring
  have hb (n : ℕ) : -(2*w^(n+1)) ≤ poleCoeff a (n+1)*w^(n+1) := by
    have hc := (abs_le.mp (poleCoeff_bound a ha (n+1))).1
    have hp : 0 ≤ w^(n+1) := pow_nonneg hw0 _
    nlinarith
  have hsum := hg.neg.tsum_le_tsum hb htail
  have hgeo : (∑' n : ℕ, 2*w^(n+1)) = 2*w/(1-w) := by
    have he : (fun n : ℕ => 2*w^(n+1)) = fun n => (2*w)*w^n := by
      funext n
      simp only [pow_succ]
      ring
    rw [he,tsum_mul_left,tsum_geometric_of_abs_lt_one hwabs]
    ring
  have hdecomp : pole a z = 1 + ∑' n : ℕ, poleCoeff a (n+1)*w^(n+1) := by
    change (∑' n : ℕ, poleCoeff a n*w^n) = _
    rw [hs.tsum_eq_zero_add]
    simp [poleCoeff]
  rw [tsum_neg,hgeo] at hsum
  rw [hdecomp]
  have hden : 0 < 1-w := by linarith
  have hfrac : 2*w/(1-w) ≤ 2/3 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith
#print axioms OQ14.Packet06ConePolePositive.pole_positive_near_north
end OQ14.Packet06ConePolePositive

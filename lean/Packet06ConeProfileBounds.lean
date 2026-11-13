import Packet06ConeUniformBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeProfileBounds
open Set OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville Packet06ConeUniformBounds

theorem profile_slope_uniform (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) 2, ∀ z ∈ Icc (-1 : ℝ) 1,
      |profile a t z| ≤ C ∧ |CapSturmLiouville.slope a t z| ≤ C := by
  let ρ := max (t^2) ((1-t)/2)
  have hρ : 0 < ρ := lt_of_lt_of_le (sq_pos_of_pos ht) (le_max_left _ _)
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply max_lt
    · nlinarith
    · linarith
  have htm : |t| ≤ 1 := by rw [abs_of_pos ht]; linarith
  have htρ : |t^2| ≤ ρ := by rw [abs_of_nonneg (sq_nonneg t)]; exact le_max_left _ _
  have hptρ : |(1-t)/2| ≤ ρ := by rw [abs_of_nonneg (by linarith : 0 ≤ (1-t)/2)]; exact le_max_right _ _
  let M := majorant ρ
  have hM : 0 ≤ M := majorant_nonnegative ρ hρ.le
  refine ⟨3*M^2,by positivity,?_⟩
  intro a ha z hz
  have hpt := pole_bound a t ρ ha hρ hρ1 hptρ
  have hpd := poleD_bound a t ρ ha hρ hρ1 hptρ
  have hot := odd_bound a t ρ ha hρ hρ1 htm htρ
  have hod := oddD_bound a t ρ ha hρ hρ1 htm htρ
  change |pole a t| ≤ M at hpt
  change |poleD a t| ≤ M at hpd
  change |odd a t| ≤ M at hot
  change |oddD a t| ≤ 3*M at hod
  by_cases hneg : z < -t
  · have hnz : |(1-(-z))/2| ≤ ρ := by
      rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ (1-(-z))/2)]
      exact le_trans (by linarith) (le_max_right _ _)
    have hp := pole_bound a (-z) ρ ha hρ hρ1 hnz
    have hd := poleD_bound a (-z) ρ ha hρ hρ1 hnz
    change |pole a (-z)| ≤ M at hp
    change |poleD a (-z)| ≤ M at hd
    simp only [profile,CapSturmLiouville.slope,if_pos hneg,negative,negativeD,
      CapAngularShooting.exterior,exteriorD,abs_neg,abs_mul]
    constructor <;> nlinarith [mul_le_mul hot hp (abs_nonneg _) hM, mul_le_mul hot hd (abs_nonneg _) hM]
  · by_cases hmid : z ≤ t
    · have hzabs : |z| ≤ t := abs_le.mpr ⟨by linarith, hmid⟩
      have hz1 : |z| ≤ 1 := hzabs.trans ht1.le
      have hzρ : |z^2| ≤ ρ := by
        rw [abs_of_nonneg (sq_nonneg z)]
        have hs : z^2 ≤ t^2 := by nlinarith [abs_nonneg z, abs_le.mp hzabs]
        exact hs.trans (le_max_left _ _)
      have hp := odd_bound a z ρ ha hρ hρ1 hz1 hzρ
      have hd := oddD_bound a z ρ ha hρ hρ1 hz1 hzρ
      change |odd a z| ≤ M at hp
      change |oddD a z| ≤ 3*M at hd
      simp only [profile,CapSturmLiouville.slope,if_neg hneg,if_pos hmid,
        CapAngularShooting.interior,interiorD,abs_mul]
      constructor <;> nlinarith [mul_le_mul hpt hp (abs_nonneg _) hM, mul_le_mul hpt hd (abs_nonneg _) hM]
    · have hpz : |(1-z)/2| ≤ ρ := by
        rw [abs_of_nonneg (by linarith [hz.2] : 0 ≤ (1-z)/2)]
        exact le_trans (by linarith) (le_max_right _ _)
      have hp := pole_bound a z ρ ha hρ hρ1 hpz
      have hd := poleD_bound a z ρ ha hρ hρ1 hpz
      change |pole a z| ≤ M at hp
      change |poleD a z| ≤ M at hd
      simp only [profile,CapSturmLiouville.slope,if_neg hneg,if_neg hmid,
        CapAngularShooting.exterior,exteriorD,abs_mul]
      constructor <;> nlinarith [mul_le_mul hot hp (abs_nonneg _) hM, mul_le_mul hot hd (abs_nonneg _) hM]
#print axioms OQ14.Packet06ConeProfileBounds.profile_slope_uniform
end OQ14.Packet06ConeProfileBounds

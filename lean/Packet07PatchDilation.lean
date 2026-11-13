import Packet07MaxwellTranslation

/-! Scale a normalized unit-disk center configuration into an arbitrary open patch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PatchDilation
open Set Metric
abbrev Plane := Packet07PlanarCenters.Plane

/-- A sufficiently small scaled unit disk, translated to an interior point,
    lies in the prescribed open patch. -/
theorem scaled_points_inside (P : Set Plane) (hP : IsOpen P) (u : Plane) (hu : u ∈ P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (s : ℝ), 0 < s → s⁻¹ < ε →
      ∀ v : Plane, v ∈ ball (0 : Plane) 1 → u + s⁻¹ • v ∈ P := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hP u hu
  refine ⟨ε,hε,?_⟩
  intro s hs hsmall v hv
  apply hball
  rw [mem_ball, dist_eq_norm]
  have hnorm : ‖v‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hv
  have heq : u + s⁻¹ • v - u = s⁻¹ • v := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  nlinarith [inv_pos.mpr hs, norm_nonneg v]

/-- The small auxiliary frequency can be chosen independently of its geometry
    so that the target-frequency dilation fits inside the patch. -/
theorem choose_auxiliary_frequency (δ target ε : ℝ) (hδ : 0 < δ)
    (htarget : 0 < target) (hε : 0 < ε) :
    ∃ k : ℝ, 0 < k ∧ k < δ ∧ (target/k)⁻¹ < ε := by
  let k := min δ (target*ε)/2
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k,hk,?_,?_⟩
  · have := min_le_left δ (target*ε)
    dsimp [k]
    linarith
  · have hm := min_le_right δ (target*ε)
    have hbound : k < target*ε := by dsimp [k]; nlinarith
    rw [inv_div]
    apply (div_lt_iff₀ htarget).mpr
    simpa only [mul_comm] using hbound

end OQ14.Packet07PatchDilation
#print axioms OQ14.Packet07PatchDilation.scaled_points_inside
#print axioms OQ14.Packet07PatchDilation.choose_auxiliary_frequency

import Packet06LocalizedVolumeState

/-! The larger trace ball of a localized mode remains in the positive
material host and the same enclosing physical support ball after placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06LargeTraceBallHost
open Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06CyclicRotation
abbrev Space := Maxwell.Space

theorem placed_large_ball {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (j : ℕ) (i : Fin N) (s : ℝ) (hs : 0 < s) (a : Space) :
    let h := placement s hs a
    closedBall (h (g.center i)) (g.radius/s) ⊆ closedBall (0 : Space) (1/s+‖a‖) ∧
    ∀ x ∈ closedBall (h (g.center i)) (g.radius/s),
      (placedCoefficient s a (rounded n hn g η hη j)).value (VectorFourier.coordinateMap x) ≠ 0 := by
  let h := placement s hs a
  have hK : closedBall (g.center i) g.radius ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  have himage : closedBall (h (g.center i)) (g.radius/s) ⊆ h '' ball (0 : Space) 1 := by
    rw [← image_closedBall]
    exact image_subset h hK
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := himage hx
    have hy' : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
    have hs0 : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
    rw [mem_closedBall_zero_iff]
    change ‖a + s⁻¹ • rotate y‖ ≤ 1/s+‖a‖
    calc
      _ ≤ ‖a‖ + ‖s⁻¹ • rotate y‖ := norm_add_le _ _
      _ = ‖a‖ + s⁻¹*‖y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs0,rotate_norm]
      _ ≤ ‖a‖ + s⁻¹*1 := add_le_add_left (mul_le_mul_of_nonneg_left hy' hs0) _
      _ = _ := by simp [one_div,add_comm]
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := himage hx
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb : unrotate (s • (h y-a))=y := h.symm_apply_apply y
    rw [hb]
    exact (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j y hy).ne'
end OQ14.Packet06LargeTraceBallHost
#print axioms OQ14.Packet06LargeTraceBallHost.placed_large_ball

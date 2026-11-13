import Packet06ModalRetainedExistence

/-! Positive host neighborhoods retained by the actual modal construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet06ModalRetainedHost
open Set Metric Maxwell Packet06ModalHotspotExistence
  Packet06ModalRetainedExistence Packet06PlacementHomeomorph
abbrev Space := Maxwell.Space

theorem observation_in_host {N : ℕ} (d : Device N) (h : Retained d) (i : Fin N) :
    closedBall (d.center i) d.radius ⊆ d.outerBody := by
  have hb : closedBall (d.geometry.center i) d.baseRadius ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall (h.base_radius_lt.le.trans d.geometry.radius_outer)).trans
      (d.geometry.outer_inside i)
  have hi := Set.image_subset d.map hb
  change placement d.dilation d.dilation_pos d.translation ''
      closedBall (d.geometry.center i) d.baseRadius ⊆ d.outerBody at hi
  rw [image_closedBall] at hi
  exact hi

theorem supportRadius_nonneg {N : ℕ} (d : Device N) : 0 ≤ d.supportRadius := by
  dsimp [Device.supportRadius]
  exact add_nonneg (div_nonneg (by norm_num) d.dilation_pos.le) (norm_nonneg _)

theorem host_enclosed {N : ℕ} (d : Device N) :
    d.outerBody ⊆ closedBall (0 : Space) d.supportRadius := by
  rintro x ⟨y,hy,rfl⟩
  have hy' : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
  have hs : 0 ≤ d.dilation⁻¹ := (inv_pos.mpr d.dilation_pos).le
  rw [mem_closedBall_zero_iff]
  change ‖d.translation + d.dilation⁻¹ • Packet06CyclicRotation.rotate y‖ ≤
    1/d.dilation+‖d.translation‖
  calc
    _ ≤ ‖d.translation‖ + ‖d.dilation⁻¹ • Packet06CyclicRotation.rotate y‖ := norm_add_le _ _
    _ = ‖d.translation‖ + d.dilation⁻¹ * ‖y‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
      rw [Packet06CyclicRotation.rotate_norm]
    _ ≤ ‖d.translation‖ + d.dilation⁻¹ * 1 :=
      add_le_add_left (mul_le_mul_of_nonneg_left hy' hs) _
    _ = _ := by simp [one_div,add_comm]

theorem host_positive {N : ℕ} (d : Device N) (K target Q ρ M : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) (hv : Valid d K target Q ρ M P)
    (x : Space) (hx : x ∈ d.outerBody) :
    0 < d.material.value (VectorFourier.coordinateMap x) := by
  have he := hv.material_values x
  change 1+d.material.value (VectorFourier.coordinateMap x)=_ at he
  have hn := d.hn
  have hη := d.hη
  classical
  split_ifs at he with hi
  · nlinarith [sq_nonneg d.n,mul_pos hη (sq_pos_of_pos (show 0 < d.n by linarith))]
  · nlinarith

end OQ14.Packet06ModalRetainedHost
#print axioms OQ14.Packet06ModalRetainedHost.observation_in_host
#print axioms OQ14.Packet06ModalRetainedHost.supportRadius_nonneg
#print axioms OQ14.Packet06ModalRetainedHost.host_enclosed
#print axioms OQ14.Packet06ModalRetainedHost.host_positive

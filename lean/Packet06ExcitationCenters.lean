import Packet06SphereLocalField
import Packet06ConeUnionSymmetry
import Packet07FiniteSeparation

/-! Concrete finite, separated cone centers where the same sphere mode is nonzero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet06ExcitationCenters
open Metric Set
abbrev Space := Maxwell.Space

def center (N : ℕ) (r : ℝ) (i : Fin N) : Space :=
  EuclideanSpace.single 2 (Packet07PlanarCenters.offset N (r/2) i)

theorem finite_centers (N : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ (c : Fin N → Space) (a : ℝ),
      Packet06ConeUnionSymmetry.OnAxis c ∧ Function.Injective c ∧ 0 < a ∧
      (∀ i, closedBall (c i) (2*a) ⊆ ball 0 r) ∧
      (∀ i j, i ≠ j → 4*a < dist (c i) (c j)) := by
  let c := center N r
  have hi : Function.Injective c := by
    intro i j h
    have he := congrArg (fun x : Space => x 2) h
    simp only [c,center,EuclideanSpace.single_apply,ite_true] at he
    have hp : Packet07PlanarCenters.planarPoint N 0 (r/2) i =
        Packet07PlanarCenters.planarPoint N 0 (r/2) j := by
      simp only [Packet07PlanarCenters.planarPoint,he]
    exact Packet07PlanarCenters.planarPoint_injective N 0 (r/2) (by positivity) hp
  obtain ⟨b,hb,hsep⟩ := Packet07FiniteSeparation.separated_radius c hi
  let a := min b (r/8)
  have ha : 0 < a := lt_min hb (by positivity)
  refine ⟨c,a,?_,hi,ha,?_,?_⟩
  · intro i
    simp [c,center]
  · intro i x hx
    have hc : ‖c i‖ ≤ r/2 := by
      rw [show c i=EuclideanSpace.single 2 (Packet07PlanarCenters.offset N (r/2) i) from rfl,
        EuclideanSpace.norm_single,Real.norm_eq_abs,
        abs_of_pos (Packet07PlanarCenters.offset_positive N (r/2) (by positivity) i)]
      exact Packet07PlanarCenters.offset_le N (r/2) (by positivity) i
    have hx' : dist x (c i) ≤ 2*a := hx
    have ht := dist_triangle x (c i) 0
    rw [dist_zero_right,dist_zero_right] at ht
    have ha8 : a ≤ r/8 := min_le_right _ _
    change ‖x-0‖ < r
    simp only [sub_zero]
    linarith
  · intro i j hij
    have hab : a ≤ b := min_le_left _ _
    linarith [hsep i j hij]

theorem sphere_excitation_centers (N : ℕ) (n : ℝ) (hn : 1 < n)
    (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ (c : Fin N → Space) (a : ℝ),
      Packet06ConeUnionSymmetry.OnAxis c ∧ Function.Injective c ∧ 0 < a ∧
      (∀ i, closedBall (c i) (2*a) ⊆ ball 0 1) ∧
      (∀ i j, i ≠ j → 4*a < dist (c i) (c j)) ∧
      (∀ i x, x ∈ closedBall (c i) (2*a) →
        Packet06SphereLocalField.inner n z w x 2 ≠ 0) := by
  obtain ⟨r,hr,hr1,hE⟩ := Packet06SphereLocalField.axial_nonzero_near_center n hn z w hz hw
  obtain ⟨c,a,haxis,hi,ha,hball,hsep⟩ := finite_centers N r hr
  refine ⟨c,a,haxis,hi,ha,?_,hsep,?_⟩
  · intro i
    exact (hball i).trans (ball_subset_ball hr1.le)
  · intro i x hx
    apply hE
    simpa only [mem_ball,dist_zero_right] using hball i hx

end OQ14.Packet06ExcitationCenters
#print axioms OQ14.Packet06ExcitationCenters.finite_centers
#print axioms OQ14.Packet06ExcitationCenters.sphere_excitation_centers

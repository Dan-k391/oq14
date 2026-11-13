import Packet05FiniteBranchMaximum
import Packet06PhysicalPlacement
import Mathlib.Topology.Order.IntermediateValue

/-! Axial orbits move attained branch maxima into the eventual observation plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet07MeridionalMaximum
open Set Maxwell ModalAxialRotation

theorem orbit_meets_meridian (x : Space) : ∃ θ : ℝ, spatial θ x 1=0 := by
  let f : ℝ → ℝ := fun θ => Real.sin θ*x 0+Real.cos θ*x 1
  have hf : Continuous f := (Real.continuous_sin.mul continuous_const).add
    (Real.continuous_cos.mul continuous_const)
  have h0 : f 0=x 1 := by simp [f]
  have hπ : f Real.pi= -x 1 := by simp [f]
  have hmem : (0 : ℝ) ∈ f '' Icc 0 Real.pi := by
    rcases le_total (x 1) 0 with h | h
    · apply intermediate_value_Icc Real.pi_pos.le hf.continuousOn
      rw [h0,hπ]
      exact ⟨h,by linarith⟩
    · apply intermediate_value_Icc' Real.pi_pos.le hf.continuousOn
      rw [h0,hπ]
      exact ⟨by linarith,h⟩
  obtain ⟨θ,_,hθ⟩ := hmem
  refine ⟨θ,?_⟩
  simpa only [f,spatial,WithLp.equiv_symm_pi_apply,Matrix.cons_val_one,Matrix.head_cons] using hθ

theorem finite_branches_meridional_maximum {J : Type*} [Fintype J]
    (K : Set Space) (hK : IsCompact K) (hne : K.Nonempty)
    (D : J → Set Space) (hclosed : ∀ j, IsClosed (D j))
    (hcover : K ⊆ ⋃ j,D j) (amp : J → Space → ℝ)
    (hcont : ∀ j, ContinuousOn (amp j) (K ∩ D j))
    (hrot : ∀ θ j x, x ∈ K ∩ D j → spatial θ x ∈ K ∩ D j)
    (hamp : ∀ θ j x, x ∈ K ∩ D j → amp j (spatial θ x)=amp j x) :
    ∃ j x, x ∈ K ∩ D j ∧ x 1=0 ∧
      ∀ j' y, y ∈ K ∩ D j' → amp j' y ≤ amp j x := by
  obtain ⟨j,x,hx,hmax⟩ := Packet05FiniteBranchMaximum.finite_closed_branches_attain_max
    K hK hne D hclosed hcover amp hcont
  obtain ⟨θ,hθ⟩ := orbit_meets_meridian x
  refine ⟨j,spatial θ x,hrot θ j x hx,hθ,?_⟩
  intro j' y hy
  rw [hamp θ j x hx]
  exact hmax j' y hy

theorem placed_meridian_is_planar (s : ℝ) (a x : Space) (ha : a 2=0) (hx : x 1=0) :
    Packet06PhysicalPlacement.point s a x 2=0 := by
  simp [Packet06PhysicalPlacement.point,Packet06CyclicRotation.rotate,WeakCurl.previous,
    PiLp.add_apply,PiLp.smul_apply,ha,hx]

end OQ14.Packet07MeridionalMaximum
#print axioms OQ14.Packet07MeridionalMaximum.orbit_meets_meridian
#print axioms OQ14.Packet07MeridionalMaximum.finite_branches_meridional_maximum
#print axioms OQ14.Packet07MeridionalMaximum.placed_meridian_is_planar

import Packet06ConcreteModalGeometry

/-! The same nonzero sphere mode permits a cone cluster in any positive ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06SmallClusterGeometry
open Metric Set Packet06ConcreteModalGeometry

theorem exists_geometry_in_ball (N : ℕ) (n : ℝ) (hn : 1 < n) (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : Geometry N n,
      (∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 δ) ∧
      (∀ i, Packet06SphereLocalField.inner n z w (g.center i) 2 ≠ 0) := by
  obtain ⟨r₀,hr₀,hr₁,hE⟩ :=
    Packet06SphereLocalField.axial_nonzero_near_center n hn z w hz hw
  let r := min r₀ δ
  have hr : 0 < r := lt_min hr₀ hδ
  obtain ⟨c,a,haxis,hi,ha,hball,hsep⟩ := Packet06ExcitationCenters.finite_centers N r hr
  let χ : ContDiffBump (0 : Maxwell.Space) := ⟨a,2*a,ha,by linarith⟩
  obtain ⟨p,hχ,hcontrast,hthreshold,hν,_⟩ :=
    ConicalFamily.exists_data χ (n^2) (3/4) (by nlinarith) (by norm_num) (by norm_num)
  let b := min (a/2) (1/2)
  have hb : 0 < b := lt_min (by positivity) (by norm_num)
  have hba : b ≤ a/2 := min_le_left _ _
  let g : Geometry N n := {
    center := c
    datum := p
    radius := b
    onAxis := haxis
    injective := hi
    contrast := hcontrast
    threshold := hthreshold
    singular := hν
    radius_pos := hb
    radius_lt_one := (min_le_right _ _).trans_lt (by norm_num)
    radius_inner := by rw [hχ]; change b<a; linarith
    radius_outer := by rw [hχ]; change b≤2*a; linarith
    outer_inside := by
      rw [hχ]
      intro i
      exact (hball i).trans (ball_subset_ball ((min_le_left _ _).trans hr₁.le))
    outer_disjoint := by rw [hχ]; exact Packet07FiniteSeparation.disjoint_outer_balls c a hsep
    separated := by intro i j hij; linarith [hsep i j hij] }
  refine ⟨g,?_,?_⟩
  · change ∀ i, closedBall (c i) p.cutoff.rOut ⊆ ball 0 δ
    rw [hχ]
    exact fun i => (hball i).trans (ball_subset_ball (min_le_right _ _))
  · intro i
    apply hE
    have hc := hball i (mem_closedBall_self (by positivity : 0 ≤ 2*a))
    have hc' := (ball_subset_ball (min_le_left r₀ δ)) hc
    simpa only [mem_ball,dist_zero_right] using hc'

end OQ14.Packet06SmallClusterGeometry
#print axioms OQ14.Packet06SmallClusterGeometry.exists_geometry_in_ball

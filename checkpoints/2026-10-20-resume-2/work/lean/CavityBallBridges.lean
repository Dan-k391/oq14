import CavityBallGeometry

/-! # Actual interface balls inside a spherical cavity -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.CavityBallBridges

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open OQ14.DisjointBallGeometry OQ14.DisjointBallCells OQ14.CavityBallGeometry
open scoped Topology

theorem exists_small_ball_subset (Ω : Set Space) (hΩ : IsOpen Ω) (p : Space)
    (hp : p ∈ Ω) (b : ℝ) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < b ∧ ball p δ ⊆ Ω := by
  obtain ⟨d,hd,hdΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  let δ := min d b/2
  have hδ : 0 < δ := half_pos (lt_min hd hb)
  exact ⟨δ,hδ,(half_lt_self (lt_min hd hb)).trans_le (min_le_right _ _),
    (ball_subset_ball ((half_lt_self (lt_min hd hb)).le.trans (min_le_left _ _))).trans hdΩ⟩

theorem inclusion_cavity_bridge {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (L : ℝ) (hr : ∀ i, 0 < radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) (i : ι) :
    Bridge (ball (center i) (radius i)) (cavity center radius L) := by
  classical
  let p := point (center i) (radius i)
  let others : {j : ι // j ≠ i} → Space := fun j => center j
  let otherRadius : {j : ι // j ≠ i} → ℝ := fun j => radius j
  let Ω := ball (0 : Space) L ∩ exterior others otherRadius
  have hpdist : dist p (center i) = radius i := by
    rw [point_dist_center,abs_of_pos (hr i)]
  have hpCore : p ∈ ball (0 : Space) L := by
    have ht := norm_add_le (p-center i) (center i)
    rw [sub_add_cancel,← dist_eq_norm,hpdist] at ht
    exact mem_ball_zero_iff.mpr (by linarith [hcore i])
  have hpOther : p ∈ exterior others otherRadius := by
    intro j
    have ht := dist_triangle (center i) p (center j)
    rw [dist_comm (center i) p,hpdist] at ht
    have hs := hsep i j (Ne.symm j.property)
    dsimp [others,otherRadius]
    linarith
  obtain ⟨δ,hδ,hδr,hδΩ⟩ := exists_small_ball_subset Ω
    (isOpen_ball.inter (exterior_isOpen others otherRadius)) p ⟨hpCore,hpOther⟩
    (radius i) (hr i)
  have hother (x : Space) (hx : x ∈ ball p δ) (j : ι) (hji : j ≠ i) :
      radius j < dist x (center j) := (hδΩ hx).2 ⟨j,hji⟩
  refine ⟨ball p δ,isOpen_ball,isConnected_ball hδ,?_,?_,?_⟩
  · filter_upwards [ae_dist_ne (center i) (radius i)] with x hx hb
    rcases lt_or_gt_of_ne hx with hinside | houtside
    · exact Or.inl hinside
    · right
      refine ⟨(hδΩ hb).1,fun j => ?_⟩
      by_cases hji : j = i
      · simpa only [hji] using houtside
      · exact hother x hb j hji
  · refine ⟨point (center i) (radius i-δ/2),?_,?_⟩
    · change dist (point (center i) (radius i-δ/2)) (point (center i) (radius i)) < δ
      rw [point_dist,show radius i-δ/2-radius i = -(δ/2) by ring,
        abs_neg,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    · change dist (point (center i) (radius i-δ/2)) (center i) < radius i
      rw [point_dist_center,abs_of_pos (by linarith [hr i])]
      linarith
  · let x := point (center i) (radius i+δ/2)
    have hb : x ∈ ball p δ := by
      change dist (point (center i) (radius i+δ/2)) (point (center i) (radius i)) < δ
      rw [point_dist,show radius i+δ/2-radius i = δ/2 by ring,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    refine ⟨x,hb,(hδΩ hb).1,fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      change radius i < dist (point (center i) (radius i+δ/2)) (center i)
      rw [point_dist_center,abs_of_pos (by linarith [hr i])]
      linarith
    · exact hother x hb j hji

theorem cavity_shell_bridge {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (L U : ℝ) (hL : 0 < L) (hLU : L < U)
    (hcore : ∀ i, ‖center i‖+radius i < L) :
    Bridge (cavity center radius L) (OQ14.RadialMaterialCells.annulus L U) := by
  let p := OQ14.RadialMaterialCells.axis L
  let Ω := ball (0 : Space) U ∩ exterior center radius
  have hpNorm : ‖p‖ = L := by rw [OQ14.RadialMaterialCells.axis_norm,abs_of_pos hL]
  have hpCore : p ∈ ball (0 : Space) U := mem_ball_zero_iff.mpr (by rwa [hpNorm])
  have hpOther : p ∈ exterior center radius := by
    intro i
    have ht := norm_add_le (p-center i) (center i)
    rw [sub_add_cancel,hpNorm,← dist_eq_norm] at ht
    linarith [hcore i]
  obtain ⟨δ,hδ,hδL,hδΩ⟩ := exists_small_ball_subset Ω
    (isOpen_ball.inter (exterior_isOpen center radius)) p ⟨hpCore,hpOther⟩ L hL
  refine ⟨ball p δ,isOpen_ball,isConnected_ball hδ,?_,?_,?_⟩
  · filter_upwards [OQ14.RadialMaterialCells.ae_norm_ne L] with x hx hb
    rcases lt_or_gt_of_ne hx with hinside | houtside
    · exact Or.inl ⟨mem_ball_zero_iff.mpr hinside,(hδΩ hb).2⟩
    · exact Or.inr ⟨houtside,mem_ball_zero_iff.mp (hδΩ hb).1⟩
  · let x := OQ14.RadialMaterialCells.axis (L-δ/2)
    have hb : x ∈ ball p δ := by
      rw [mem_ball,OQ14.RadialMaterialCells.axis_dist,
        show L-δ/2-L = -(δ/2) by ring,abs_neg,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    refine ⟨x,hb,?_,(hδΩ hb).2⟩
    apply mem_ball_zero_iff.mpr
    rw [OQ14.RadialMaterialCells.axis_norm,abs_of_pos (by linarith : 0 < L-δ/2)]
    linarith
  · let x := OQ14.RadialMaterialCells.axis (L+δ/2)
    have hb : x ∈ ball p δ := by
      rw [mem_ball,OQ14.RadialMaterialCells.axis_dist,
        show L+δ/2-L = δ/2 by ring,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    refine ⟨x,hb,?_,mem_ball_zero_iff.mp (hδΩ hb).1⟩
    rw [OQ14.RadialMaterialCells.axis_norm,abs_of_pos (by linarith : 0 < L+δ/2)]
    linarith

end OQ14.CavityBallBridges

#print axioms OQ14.CavityBallBridges.exists_small_ball_subset
#print axioms OQ14.CavityBallBridges.inclusion_cavity_bridge
#print axioms OQ14.CavityBallBridges.cavity_shell_bridge

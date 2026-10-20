import DisjointBallGeometry

/-! # Concrete material cells for separated spherical inclusions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.DisjointBallCells

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open OQ14.DisjointBallGeometry
open scoped Topology

def cell {ι : Type*} (center : ι → Space) (radius : ι → ℝ) : Option ι → Set Space
  | none => exterior center radius
  | some i => ball (center i) (radius i)

theorem cell_open {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (i : Option ι) : IsOpen (cell center radius i) := by
  cases i with
  | none => exact exterior_isOpen center radius
  | some i => exact isOpen_ball

theorem cell_preconnected {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i : Option ι) : IsPreconnected (cell center radius i) := by
  cases i with
  | none => exact (exterior_isConnected center radius hr hsep).isPreconnected
  | some i => exact (convex_ball (center i) (radius i)).isPreconnected

theorem ae_dist_ne (c : Space) (r : ℝ) : ∀ᵐ x : Space, dist x c ≠ r := by
  have hs : (volume : Measure Space) (sphere c r) = 0 := Measure.addHaar_sphere volume c r
  simpa only [ae_iff,ne_eq,not_not,sphere] using hs

theorem ae_cell_cover {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ) :
    ∀ᵐ x : Space, ∃ i, x ∈ cell center radius i := by
  classical
  have hn : ∀ᵐ x : Space, ∀ i, dist x (center i) ≠ radius i :=
    ae_all_iff.mpr (fun i => ae_dist_ne (center i) (radius i))
  filter_upwards [hn] with x hx
  by_cases he : x ∈ exterior center radius
  · exact ⟨none,he⟩
  · have hi : ∃ i, ¬ radius i < dist x (center i) := by
      simpa only [DisjointBallGeometry.exterior,mem_setOf_eq,not_forall] using he
    obtain ⟨i,hi⟩ := hi
    exact ⟨some i,lt_of_le_of_ne (not_lt.mp hi) (hx i)⟩

def point (c : Space) (r : ℝ) : Space := c+OQ14.RadialMaterialCells.axis r

theorem point_dist_center (c : Space) (r : ℝ) : dist (point c r) c = |r| := by
  rw [point,dist_eq_norm,add_sub_cancel_left,OQ14.RadialMaterialCells.axis_norm]

theorem point_dist (c : Space) (r s : ℝ) : dist (point c r) (point c s) = |r-s| := by
  simp only [point,dist_eq_norm,add_sub_add_left_eq_sub]
  exact OQ14.RadialMaterialCells.axis_dist r s

theorem inclusion_exterior_bridge {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (hr : ∀ i, 0 < radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) (i : ι) :
    Bridge (ball (center i) (radius i)) (exterior center radius) := by
  classical
  let p := point (center i) (radius i)
  have hp : dist p (center i) = radius i := by
    rw [point_dist_center,abs_of_pos (hr i)]
  let g : Option ι → ℝ
    | none => radius i
    | some j => if j = i then radius i else dist p (center j)-radius j
  have hg : ∀ j, 0 < g j := by
    intro j
    cases j with
    | none => exact hr i
    | some j =>
      by_cases hji : j = i
      · simpa only [g,if_pos hji] using hr i
      · have ht := dist_triangle (center i) p (center j)
        rw [dist_comm (center i) p,hp] at ht
        have hs := hsep i j (Ne.symm hji)
        simp only [g,if_neg hji]
        linarith
  obtain ⟨δ,hδ,hgδ⟩ := exists_positive_uniform_lt g hg
  have hδr : δ < radius i := hgδ none
  have hother (x : Space) (hx : x ∈ ball p δ) (j : ι) (hji : j ≠ i) :
      radius j < dist x (center j) := by
    have hd := hgδ (some j)
    simp only [g,if_neg hji] at hd
    have ht := dist_triangle p x (center j)
    rw [dist_comm p x] at ht
    have hx' : dist x p < δ := hx
    linarith
  refine ⟨ball p δ,isOpen_ball,isConnected_ball hδ,?_,?_,?_⟩
  · filter_upwards [ae_dist_ne (center i) (radius i)] with x hx hb
    rcases lt_or_gt_of_ne hx with hinside | houtside
    · exact Or.inl hinside
    · right
      intro j
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
    refine ⟨x,hb,fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      change radius i < dist (point (center i) (radius i+δ/2)) (center i)
      rw [point_dist_center,abs_of_pos (by linarith [hr i])]
      linarith
    · exact hother x hb j hji

theorem cells_reachable {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i j : Option ι) :
    Relation.ReflTransGen (fun i j => Bridge (cell center radius i) (cell center radius j)) i j := by
  have hto (i : Option ι) :
      Relation.ReflTransGen (fun i j => Bridge (cell center radius i) (cell center radius j))
        i none := by
    cases i with
    | none => exact Relation.ReflTransGen.refl
    | some i => exact Relation.ReflTransGen.single (inclusion_exterior_bridge center radius hr hsep i)
  exact (hto i).trans (reachable_symm (cell center radius) (hto j))

end OQ14.DisjointBallCells

#print axioms OQ14.DisjointBallCells.cell_open
#print axioms OQ14.DisjointBallCells.cell_preconnected
#print axioms OQ14.DisjointBallCells.ae_dist_ne
#print axioms OQ14.DisjointBallCells.ae_cell_cover
#print axioms OQ14.DisjointBallCells.point_dist_center
#print axioms OQ14.DisjointBallCells.point_dist
#print axioms OQ14.DisjointBallCells.inclusion_exterior_bridge
#print axioms OQ14.DisjointBallCells.cells_reachable

import RadialMaterialCells
import PiecewiseMaxwellUniqueness

/-! # Actual finite concentric material partitions

Strictly ordered positive radii determine literal open radial cells. Their
exceptional interface spheres have zero volume. Actual adjacent bridges and
finite graph induction supply all geometric fields of the Maxwell partition.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.FiniteRadialPartition

open MeasureTheory Metric Set OQ14.Maxwell OQ14.RadialMaterialCells
  OQ14.MaterialCellGraph
open scoped Topology

def cell {n : ℕ} (r : Fin (n+1) → ℝ) (j : Fin (n+2)) : Set Space :=
  {x | (∀ i : Fin (n+1), i.val < j.val → r i < ‖x‖) ∧
    (∀ i : Fin (n+1), j.val ≤ i.val → ‖x‖ < r i)}

theorem cell_zero {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r) :
    cell r 0 = inner (r 0) := by
  ext x
  constructor
  · intro hx
    exact mem_ball_zero_iff.mpr (hx.2 0 (by simp))
  · intro hx
    have hnorm : ‖x‖ < r 0 := mem_ball_zero_iff.mp hx
    refine ⟨fun i hi => by change i.val < 0 at hi; omega, fun i _ => ?_⟩
    exact lt_of_lt_of_le hnorm (hm.monotone (Fin.zero_le i))

theorem cell_middle {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (j : Fin (n+2)) (hj : 0 < j.val) (hn : j.val < n+1) :
    cell r j = annulus (r ⟨j.val-1,by omega⟩) (r ⟨j.val,hn⟩) := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1 ⟨j.val-1,by omega⟩ (by change j.val-1 < j.val; omega),
      hx.2 ⟨j.val,hn⟩ le_rfl⟩
  · intro hx
    constructor
    · intro i hi
      exact lt_of_le_of_lt (hm.monotone (show i ≤ ⟨j.val-1,by omega⟩ by
        change i.val ≤ j.val-1; omega)) hx.1
    · intro i hi
      exact lt_of_lt_of_le hx.2 (hm.monotone (show (⟨j.val,hn⟩ : Fin (n+1)) ≤ i from hi))

theorem cell_last {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r) :
    cell r (Fin.last (n+1)) = exterior (r (Fin.last n)) := by
  ext x
  constructor
  · intro hx
    exact hx.1 (Fin.last n) (by simp)
  · intro hx
    refine ⟨fun i _ => ?_,fun i hi => by have := i.isLt; simp at hi; omega⟩
    exact lt_of_le_of_lt (hm.monotone (Fin.le_last i)) hx

theorem cell_open {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (j : Fin (n+2)) : IsOpen (cell r j) := by
  by_cases hz : j.val = 0
  · have he : j = 0 := Fin.ext hz
    rw [he,cell_zero r hm]
    exact inner_open _
  · by_cases hn : j.val < n+1
    · rw [cell_middle r hm j (by omega) hn]
      exact annulus_open _ _
    · have he : j = Fin.last (n+1) := Fin.ext (by simp; omega)
      rw [he,cell_last r hm]
      exact exterior_open _

theorem cell_preconnected {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (j : Fin (n+2)) : IsPreconnected (cell r j) := by
  by_cases hz : j.val = 0
  · have he : j = 0 := Fin.ext hz
    rw [he,cell_zero r hm]
    exact inner_preconnected _
  · by_cases hn : j.val < n+1
    · rw [cell_middle r hm j (by omega) hn]
      exact annulus_preconnected _ _ (hp _).le
    · have he : j = Fin.last (n+1) := Fin.ext (by simp; omega)
      rw [he,cell_last r hm]
      exact exterior_preconnected _ (hp _).le

theorem exists_cell_of_norm_ne {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r) (x : Space)
    (hx : ∀ i, ‖x‖ ≠ r i) : ∃ j : Fin (n+2), x ∈ cell r j := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ.filter (fun i => ‖x‖ < r i)
  by_cases hs : S.Nonempty
  · let i := S.min' hs
    have hi : ‖x‖ < r i := (Finset.mem_filter.mp (Finset.min'_mem S hs)).2
    refine ⟨i.castSucc,?_,?_⟩
    · intro l hl
      have hn : ¬ ‖x‖ < r l := by
        intro hlt
        have hm := Finset.min'_le S l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩)
        change i ≤ l at hm
        change l.val < i.val at hl
        exact (not_le_of_gt hl) hm
      exact lt_of_le_of_ne (le_of_not_gt hn) (hx l).symm
    · intro l hl
      exact hi.trans_le (hm.monotone (show i ≤ l from hl))
  · refine ⟨Fin.last (n+1),?_,?_⟩
    · intro i _
      have hn : ¬ ‖x‖ < r i := by
        intro hi
        exact hs ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      exact lt_of_le_of_ne (le_of_not_gt hn) (hx i).symm
    · intro i hi
      have := i.isLt
      simp at hi
      omega

theorem ae_cell_cover {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r) :
    ∀ᵐ x : Space, ∃ j : Fin (n+2), x ∈ cell r j := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_norm_ne (r i))] with x hx
  exact exists_cell_of_norm_ne r hm x hx

theorem adjacent_bridge {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (i : Fin (n+1)) :
    Bridge (cell r i.castSucc) (cell r i.succ) := by
  by_cases h0 : i.val = 0
  · have hi0 : i.castSucc = 0 := Fin.ext h0
    rw [hi0,cell_zero r hm]
    by_cases hn : i.val = n
    · have hiL : i.succ = Fin.last (n+1) := Fin.ext (by simp; omega)
      rw [hiL,cell_last r hm]
      have hr : r (Fin.last n) = r 0 := congrArg r (Fin.ext (by simp; omega))
      rw [hr]
      exact inner_exterior_bridge _ (hp 0)
    · rw [cell_middle r hm i.succ (by simp) (by simp; omega)]
      have hi : i = 0 := Fin.ext h0
      change Bridge (inner (r 0)) (annulus (r i) (r ⟨i.val+1,by omega⟩))
      have hr0 : r i = r 0 := congrArg r hi
      rw [hr0]
      exact inner_annulus_bridge _ _ (hp 0) (hm (by change 0 < i.val+1; omega))
  · by_cases hn : i.val = n
    · have hiL : i.succ = Fin.last (n+1) := Fin.ext (by simp; omega)
      rw [cell_middle r hm i.castSucc (by change 0 < i.val; omega)
        (by change i.val < n+1; exact i.isLt),hiL,cell_last r hm]
      have hi : i = Fin.last n := Fin.ext hn
      change Bridge (annulus (r ⟨i.val-1,by omega⟩) (r i)) (exterior (r (Fin.last n)))
      rw [← hi]
      exact annulus_exterior_bridge _ _ (hp _).le (hm (by change i.val-1 < i.val; omega))
    · rw [cell_middle r hm i.castSucc (by change 0 < i.val; omega)
        (by change i.val < n+1; exact i.isLt),
        cell_middle r hm i.succ (by simp) (by simp; omega)]
      change Bridge (annulus (r ⟨i.val-1,by omega⟩) (r i))
        (annulus (r i) (r ⟨i.val+1,by omega⟩))
      exact annulus_bridge _ _ _ (hp _).le
        (hm (by change i.val-1 < i.val; omega)) (hm (by change i.val < i.val+1; omega))

theorem reachable_from_zero {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (j : Fin (n+2)) :
    Relation.ReflTransGen (fun i j => Bridge (cell r i) (cell r j)) 0 j := by
  have h : ∀ m : ℕ, ∀ hm : m < n+2,
      Relation.ReflTransGen (fun i j => Bridge (cell r i) (cell r j)) 0 ⟨m,hm⟩ := by
    intro m
    induction m with
    | zero => intro hzero; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hsucc
      exact (ih (by omega)).tail (adjacent_bridge r hm hp ⟨m,by omega⟩)
  exact h j.val j.isLt

theorem reachable_all {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (i j : Fin (n+2)) :
    Relation.ReflTransGen (fun i j => Bridge (cell r i) (cell r j)) i j :=
  (MaterialCellGraph.reachable_symm (cell r) (reachable_from_zero r hm hp i)).trans
    (reachable_from_zero r hm hp j)

theorem exists_exterior_seed {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (R : ℝ) :
    ∃ x : Space, x ∈ cell r (Fin.last (n+1)) ∧ R < ‖x‖ := by
  let a := max R (r (Fin.last n))+1
  have ha : 0 < a := by dsimp [a]; linarith [hp (Fin.last n),le_max_right R (r (Fin.last n))]
  have hn : ‖axis a‖ = a := by rw [axis_norm,abs_of_pos ha]
  refine ⟨axis a,?_,?_⟩
  · rw [cell_last r hm]
    change r (Fin.last n) < ‖axis a‖
    rw [hn]
    dsimp [a]
    linarith [le_max_right R (r (Fin.last n))]
  · rw [hn]
    dsimp [a]
    linarith [le_max_left R (r (Fin.last n))]

def partition {n : ℕ} (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hp : ∀ i, 0 < r i) (ε : Space → ℝ) (v : Fin (n+2) → ℝ)
    (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → ε x = v i) :
    PiecewiseMaxwellUniqueness.Partition (Fin (n+2)) ε where
  cell := cell r
  region_open := cell_open r hm
  region_preconnected := cell_preconnected r hm hp
  value := v
  positive := hv
  constant_on := hε
  cover := ae_cell_cover r hm
  reachable := reachable_all r hm hp

end OQ14.FiniteRadialPartition

#print axioms OQ14.FiniteRadialPartition.cell_zero
#print axioms OQ14.FiniteRadialPartition.cell_middle
#print axioms OQ14.FiniteRadialPartition.cell_last
#print axioms OQ14.FiniteRadialPartition.cell_open
#print axioms OQ14.FiniteRadialPartition.cell_preconnected
#print axioms OQ14.FiniteRadialPartition.exists_cell_of_norm_ne
#print axioms OQ14.FiniteRadialPartition.ae_cell_cover
#print axioms OQ14.FiniteRadialPartition.adjacent_bridge
#print axioms OQ14.FiniteRadialPartition.reachable_from_zero
#print axioms OQ14.FiniteRadialPartition.reachable_all
#print axioms OQ14.FiniteRadialPartition.exists_exterior_seed
#print axioms OQ14.FiniteRadialPartition.partition
